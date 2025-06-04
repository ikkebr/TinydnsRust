use std::collections::{HashMap, VecDeque};
use std::net::IpAddr;
use std::time::{Duration, Instant};

/// Represents the type of DNS record being cached.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RecordType {
    /// Represents an IPv4 address record.
    A,
    /// Represents an IPv6 address record.
    AAAA,
}

/// Represents an entry in the DNS cache.
/// This struct is not public as it's an internal detail.
#[derive(Debug, Clone)]
struct CacheEntry {
    ips: Vec<IpAddr>,
    expiry: Instant,
}

/// An in-memory DNS cache with Time-To-Live (TTL) support and optional max size.
///
/// The cache stores DNS records (currently A and AAAA) and evicts them when their
/// TTL expires or when the cache reaches its maximum configured size (using a FIFO strategy).
///
/// # Thread Safety
///
/// This `Cache` implementation is **not** internally thread-safe. If you need to share
/// the cache between multiple threads, you must wrap it in a synchronization primitive,
/// such as `std::sync::Arc` and `std::sync::Mutex` or `std::sync::RwLock`.
///
/// For read-heavy workloads, `Arc<RwLock<Cache>>` is generally preferred:
/// ```
/// use std::sync::{Arc, RwLock};
/// // Assuming your crate is named `tiny_dns_cache` when used externally.
/// // If used within the same crate, `Cache` would be directly available.
/// use tiny_dns_cache::Cache;
///
/// // let cache = Arc::new(RwLock::new(Cache::new(Some(1000))));
/// // For use in an async context, you might consider `tokio::sync::Mutex` or `tokio::sync::RwLock`.
/// ```
pub struct Cache {
    entries: HashMap<(String, RecordType), CacheEntry>,
    // For FIFO eviction: a queue of keys in insertion order.
    order: VecDeque<(String, RecordType)>,
    max_size: Option<usize>,
}

impl Cache {
    /// Creates a new DNS cache.
    ///
    /// `max_size` is an optional capacity limit for the cache. If `None`,
    /// the cache can grow indefinitely (until memory runs out). If `Some`,
    /// a FIFO (First-In, First-Out) eviction strategy will be used when the
    /// cache exceeds this size.
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_dns_cache::Cache; // Use the actual crate name if different
    ///
    /// // A cache with unlimited size
    /// let mut cache_unlimited = Cache::new(None);
    ///
    /// // A cache limited to 100 entries
    /// let mut cache_limited = Cache::new(Some(100));
    /// ```
    pub fn new(max_size: Option<usize>) -> Self {
        Cache {
            entries: HashMap::new(),
            order: std::collections::VecDeque::new(),
            max_size,
        }
    }

    /// Returns the number of current entries in the cache.
    ///
    /// This count includes all entries currently stored, irrespective of whether
    /// they might be expired but not yet purged or removed by a `get` operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_dns_cache::{Cache, RecordType};
    /// use std::net::Ipv4Addr;
    ///
    /// let mut cache = Cache::new(None);
    /// assert_eq!(cache.len(), 0);
    ///
    /// cache.put("example.com", RecordType::A, vec![Ipv4Addr::new(1,2,3,4).into()], 60);
    /// assert_eq!(cache.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Removes all entries from the cache.
    ///
    /// After calling this method, the cache will be empty. The `max_size` limit,
    /// if set, remains unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_dns_cache::{Cache, RecordType};
    /// use std::net::Ipv4Addr;
    ///
    /// let mut cache = Cache::new(None);
    /// cache.put("example.com", RecordType::A, vec![Ipv4Addr::new(1,2,3,4).into()], 60);
    /// assert!(!cache.len() == 0); // Cache is not empty
    ///
    /// cache.clear();
    /// assert_eq!(cache.len(), 0); // Cache is now empty
    /// ```
    pub fn clear(&mut self) {
        self.entries.clear();
        self.order.clear();
    }

    /// Adds or updates a set of IP addresses for a given domain and record type
    /// with a specified Time-To-Live (TTL).
    ///
    /// If the `domain` and `record_type` combination already exists in the cache,
    /// its IP addresses and TTL are updated. The entry is also moved to the
    /// "newest" position in the FIFO eviction queue, meaning it will be the last
    /// to be considered for eviction if the cache is full.
    ///
    /// If the cache has a `max_size` and is already full, adding a *new* entry
    /// (one not already in the cache) will cause the oldest entry to be evicted
    /// to make space. Updating an existing entry does not cause eviction of another
    /// item, even if the cache is full; it effectively replaces the old entry.
    ///
    /// # Arguments
    ///
    /// * `domain`: The domain name (e.g., "example.com").
    /// * `record_type`: The type of DNS record (`RecordType::A` or `RecordType::AAAA`).
    /// * `ips`: A vector of `IpAddr` associated with the domain and record type.
    /// * `ttl_seconds`: The Time-To-Live for this cache entry, in seconds. A TTL of 0
    ///   means the entry is considered immediately expired (or will expire very shortly after insertion).
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_dns_cache::{Cache, RecordType};
    /// use std::net::{IpAddr, Ipv4Addr};
    ///
    /// let mut cache = Cache::new(Some(10));
    /// let ip = IpAddr::V4(Ipv4Addr::new(192, 0, 2, 1));
    /// cache.put("example.com", RecordType::A, vec![ip], 300); // TTL of 5 minutes
    /// ```
    pub fn put(&mut self, domain: &str, record_type: RecordType, ips: Vec<IpAddr>, ttl_seconds: u32) {
        let expiry = Instant::now() + Duration::from_secs(ttl_seconds as u64);
        let key = (domain.to_string(), record_type.clone());

        if self.entries.contains_key(&key) {
            self.order.retain(|k| k != &key);
        }

        if self.max_size.is_some() && self.entries.len() >= self.max_size.unwrap() && !self.entries.contains_key(&key) {
            if let Some(oldest_key) = self.order.pop_front() {
                self.entries.remove(&oldest_key);
            }
        }

        self.entries.insert(key.clone(), CacheEntry { ips, expiry });
        self.order.push_back(key);
    }

    /// Retrieves a clone of non-expired IP addresses for a given domain and record type.
    ///
    /// Returns `Some(Vec<IpAddr>)` if an entry is found for the `domain` and `record_type`
    /// and it has not yet expired. The IPs are cloned to avoid direct reference to internal cache data.
    ///
    /// Returns `None` if the entry is not found in the cache or if it has expired.
    /// If an entry is found to be expired during a `get` operation, it is proactively
    /// removed from the cache.
    ///
    /// # Arguments
    ///
    /// * `domain`: The domain name to look up.
    /// * `record_type`: The type of DNS record to retrieve.
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_dns_cache::{Cache, RecordType};
    /// use std::net::{IpAddr, Ipv4Addr};
    /// use std::thread;
    /// use std::time::Duration;
    ///
    /// let mut cache = Cache::new(None);
    /// let ip = IpAddr::V4(Ipv4Addr::new(192, 0, 2, 1));
    /// cache.put("example.com", RecordType::A, vec![ip.clone()], 1); // 1 second TTL
    ///
    /// // Get immediately
    /// assert_eq!(cache.get("example.com", RecordType::A), Some(vec![ip.clone()]));
    ///
    /// // Wait for TTL to expire
    /// thread::sleep(Duration::from_secs(2));
    /// assert_eq!(cache.get("example.com", RecordType::A), None); // Entry should now be expired and removed
    /// ```
    pub fn get(&mut self, domain: &str, record_type: RecordType) -> Option<Vec<IpAddr>> {
        let key = (domain.to_string(), record_type);

        if let Some(entry) = self.entries.get(&key) {
            if Instant::now() < entry.expiry {
                return Some(entry.ips.clone());
            } else {
                self.entries.remove(&key);
                self.order.retain(|k| k != &key);
                return None;
            }
        }
        None
    }

    /// Manually triggers a scan and removal of all expired entries from the cache.
    ///
    /// This method iterates through all entries in the cache. If an entry's TTL
    /// has passed (i.e., `entry.expiry <= Instant::now()`), it is removed.
    /// This is useful for proactively cleaning up the cache, for example, by a
    /// background task, rather than relying solely on expirations detected during `get` calls.
    ///
    /// # Examples
    ///
    /// ```
    /// use tiny_dns_cache::{Cache, RecordType};
    /// use std::net::Ipv4Addr;
    /// use std::thread;
    /// use std::time::Duration;
    ///
    /// let mut cache = Cache::new(None);
    /// cache.put("ephemeral.com", RecordType::A, vec![Ipv4Addr::new(1,1,1,1).into()], 1); // 1 sec TTL
    /// cache.put("persistent.com", RecordType::A, vec![Ipv4Addr::new(2,2,2,2).into()], 300);
    ///
    /// thread::sleep(Duration::from_secs(2)); // Wait for "ephemeral.com" to expire
    ///
    /// cache.purge_expired();
    /// assert_eq!(cache.len(), 1);
    /// assert!(cache.get("persistent.com", RecordType::A).is_some());
    /// assert!(cache.get("ephemeral.com", RecordType::A).is_none());
    /// ```
    pub fn purge_expired(&mut self) {
        let now = Instant::now();
        let mut expired_keys = Vec::new();

        for (key, entry) in &self.entries {
            if entry.expiry <= now {
                expired_keys.push(key.clone());
            }
        }

        for key in expired_keys {
            self.entries.remove(&key);
            self.order.retain(|k| k != &key);
        }
    }
}

// Basic tests module
#[cfg(test)]
mod tests {
    use super::*;
    use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    use std::thread;
    use std::time::Duration;

    const TEST_DOMAIN: &str = "example.com";
    const TEST_DOMAIN_2: &str = "another.com";
    const TEST_DOMAIN_3: &str = "example.org";

    fn new_ipv4(a: u8, b: u8, c: u8, d: u8) -> IpAddr {
        IpAddr::V4(Ipv4Addr::new(a, b, c, d))
    }

    fn new_ipv6() -> IpAddr {
        IpAddr::V6(Ipv6Addr::new(0x2001, 0x0db8, 0, 0, 0, 0, 0, 0x0001))
    }

    #[test]
    fn test_put_and_get_a_record() {
        let mut cache = Cache::new(None);
        let ips = vec![new_ipv4(1, 2, 3, 4)];
        cache.put(TEST_DOMAIN, RecordType::A, ips.clone(), 60);

        let retrieved = cache.get(TEST_DOMAIN, RecordType::A);
        assert_eq!(retrieved, Some(ips));
    }

    #[test]
    fn test_put_and_get_aaaa_record() {
        let mut cache = Cache::new(None);
        let ips = vec![new_ipv6()];
        cache.put(TEST_DOMAIN, RecordType::AAAA, ips.clone(), 60);

        let retrieved = cache.get(TEST_DOMAIN, RecordType::AAAA);
        assert_eq!(retrieved, Some(ips));
    }

    #[test]
    fn test_get_non_existent() {
        let mut cache = Cache::new(None);
        let retrieved = cache.get(TEST_DOMAIN, RecordType::A);
        assert_eq!(retrieved, None);
    }

    #[test]
    fn test_ttl_expiration_with_get() {
        let mut cache = Cache::new(None);
        let ips = vec![new_ipv4(1, 1, 1, 1)];
        cache.put(TEST_DOMAIN, RecordType::A, ips.clone(), 1); // 1 second TTL

        // Should exist
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), Some(ips));

        thread::sleep(Duration::from_secs(2)); // Wait for expiration

        // Should be None and removed
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), None);
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_zero_ttl_expires_immediately() {
        let mut cache = Cache::new(None);
        let ips = vec![new_ipv4(1,1,1,1)];
        cache.put(TEST_DOMAIN, RecordType::A, ips.clone(), 0);
        // Depending on timing, it might be there for a fraction of a second.
        // To be safe, a small sleep or relying on get to clean it up.
        // For 0 TTL, it should ideally be gone by the next "tick" or access.
        thread::sleep(Duration::from_millis(50)); // Ensure time has passed
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), None);
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_purge_expired() {
        let mut cache = Cache::new(None);
        let ips1 = vec![new_ipv4(1, 1, 1, 1)];
        let ips2 = vec![new_ipv4(2, 2, 2, 2)];

        cache.put(TEST_DOMAIN, RecordType::A, ips1.clone(), 1); // Expires in 1 sec
        cache.put(TEST_DOMAIN_2, RecordType::A, ips2.clone(), 60); // Expires in 60 sec

        assert_eq!(cache.len(), 2);

        thread::sleep(Duration::from_secs(2)); // Wait for first entry to expire

        cache.purge_expired();

        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), None); // Expired one
        assert_eq!(cache.get(TEST_DOMAIN_2, RecordType::A), Some(ips2)); // Non-expired one
    }

    #[test]
    fn test_len_and_clear() {
        let mut cache = Cache::new(Some(5));
        assert_eq!(cache.len(), 0);

        cache.put(TEST_DOMAIN, RecordType::A, vec![new_ipv4(1,1,1,1)], 60);
        cache.put(TEST_DOMAIN_2, RecordType::A, vec![new_ipv4(2,2,2,2)], 60);
        assert_eq!(cache.len(), 2);

        cache.clear();
        assert_eq!(cache.len(), 0);
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), None);
        assert_eq!(cache.get(TEST_DOMAIN_2, RecordType::A), None);
    }

    #[test]
    fn test_max_size_fifo_eviction() {
        let mut cache = Cache::new(Some(2));
        let ips1 = vec![new_ipv4(1,1,1,1)];
        let ips2 = vec![new_ipv4(2,2,2,2)];
        let ips3 = vec![new_ipv4(3,3,3,3)];

        cache.put(TEST_DOMAIN, RecordType::A, ips1.clone(), 60); // Oldest
        thread::sleep(Duration::from_millis(10)); // Ensure different insertion times for order
        cache.put(TEST_DOMAIN_2, RecordType::A, ips2.clone(), 60);
        thread::sleep(Duration::from_millis(10));

        assert_eq!(cache.len(), 2);

        // This should evict TEST_DOMAIN (ips1)
        cache.put(TEST_DOMAIN_3, RecordType::A, ips3.clone(), 60);

        assert_eq!(cache.len(), 2);
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), None, "Oldest entry should be evicted");
        assert_eq!(cache.get(TEST_DOMAIN_2, RecordType::A), Some(ips2.clone()));
        assert_eq!(cache.get(TEST_DOMAIN_3, RecordType::A), Some(ips3.clone()));
    }

    #[test]
    fn test_update_existing_entry_refreshes_ttl_and_data() {
        let mut cache = Cache::new(None);
        let initial_ips = vec![new_ipv4(1,2,3,4)];
        let updated_ips = vec![new_ipv4(5,6,7,8)];

        // Initial put with short TTL
        cache.put(TEST_DOMAIN, RecordType::A, initial_ips.clone(), 1); // 1 sec TTL
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), Some(initial_ips));

        // Update the entry with new IPs and longer TTL before the original expires
        cache.put(TEST_DOMAIN, RecordType::A, updated_ips.clone(), 5); // 5 sec TTL
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), Some(updated_ips.clone()), "IPs should be updated");

        // Wait for a period longer than initial TTL but shorter than new TTL
        thread::sleep(Duration::from_secs(2));

        // Entry should still be there due to refreshed TTL
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), Some(updated_ips), "Entry should exist due to refreshed TTL");

        // Wait for new TTL to expire
        thread::sleep(Duration::from_secs(4)); // Total 2+4 = 6s, new TTL was 5s
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), None, "Entry should have expired based on new TTL");
    }

    #[test]
    fn test_update_existing_entry_at_max_capacity() {
        let mut cache = Cache::new(Some(1));
        let ips1 = vec![new_ipv4(1,1,1,1)];
        let ips2 = vec![new_ipv4(2,2,2,2)];

        cache.put(TEST_DOMAIN, RecordType::A, ips1.clone(), 60);
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), Some(ips1.clone()));
        assert_eq!(cache.len(), 1);

        // Update the existing entry. This should not cause eviction.
        cache.put(TEST_DOMAIN, RecordType::A, ips2.clone(), 60);
        assert_eq!(cache.len(), 1, "Cache length should remain 1 after update");
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), Some(ips2.clone()), "Entry should be updated");

        // Try to put a new entry, this should evict the updated TEST_DOMAIN
        let ips3 = vec![new_ipv4(3,3,3,3)];
        cache.put(TEST_DOMAIN_2, RecordType::A, ips3.clone(), 60);
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(TEST_DOMAIN, RecordType::A), None, "Original (updated) entry should be evicted");
        assert_eq!(cache.get(TEST_DOMAIN_2, RecordType::A), Some(ips3.clone()));
    }
}

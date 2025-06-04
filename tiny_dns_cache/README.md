# Tiny DNS Cache

`tiny_dns_cache` is a simple, in-memory DNS caching library for Rust. It allows you to cache DNS records (specifically A and AAAA records) with Time-To-Live (TTL) support and an optional maximum cache size with FIFO (First-In, First-Out) eviction.

This library is built using only the Rust standard library, making it lightweight with no external dependencies.

## Features

*   In-memory caching of DNS A and AAAA records.
*   Time-To-Live (TTL) support for cache entries.
*   Optional maximum cache size (`max_size`).
*   FIFO eviction policy when `max_size` is reached.
*   Manual cache entry purging (`purge_expired`).
*   Basic cache operations: `put`, `get`, `clear`, `len`.
*   No external dependencies (uses `std` only).

## Usage Example

Add this to your `Cargo.toml` (assuming you've published it or are using a local path dependency):
```toml
[dependencies]
# tiny_dns_cache = "0.1.0" # Or path = "path/to/tiny_dns_cache"
```
If you are just using it locally and `tiny_dns_cache` is a library in your current workspace, Cargo will find it. Otherwise, for a local path for an independent crate:
`tiny_dns_cache = { path = "../tiny_dns_cache" }` (adjust path as needed)

Here's a basic example of how to use the cache:

```rust
use std::net::{IpAddr, Ipv4Addr};
use std::thread;
use std::time::Duration;
use tiny_dns_cache::{Cache, RecordType}; // Adjust this 'use' statement based on your project structure

fn main() {
    // Create a cache with a maximum of 100 entries
    let mut cache = Cache::new(Some(100));

    let domain = "example.com";
    let ipv4_addr = IpAddr::V4(Ipv4Addr::new(93, 184, 216, 34));
    let ips = vec![ipv4_addr];

    // Put an A record into the cache with a TTL of 60 seconds
    cache.put(domain, RecordType::A, ips.clone(), 60);
    println!("Cached {} for {} seconds.", domain, 60);

    // Retrieve the record
    if let Some(retrieved_ips) = cache.get(domain, RecordType::A) {
        println!("Retrieved IPs for {}: {:?}", domain, retrieved_ips);
        assert_eq!(retrieved_ips, ips);
    } else {
        println!("No IPs found for {} (or expired).", domain);
    }

    // Wait for the entry to expire
    println!("Waiting for 2 seconds for the entry to potentially expire (if TTL was < 2s)...");
    // For a 60s TTL, it won't expire here. Let's test with a short TTL entry.
    let short_ttl_domain = "short.example.com";
    cache.put(short_ttl_domain, RecordType::A, ips.clone(), 1); // 1 second TTL

    thread::sleep(Duration::from_secs(2));

    if cache.get(short_ttl_domain, RecordType::A).is_none() {
        println!("Entry for {} successfully expired and was removed.", short_ttl_domain);
    } else {
        println!("Entry for {} should have expired.", short_ttl_domain);
    }

    // Manually purge any other expired entries
    cache.purge_expired();
    println!("Manually purged expired entries. Cache size: {}", cache.len());
}
```
*(Note: The `use tiny_dns_cache::{Cache, RecordType};` line in the example might need adjustment depending on how the crate is named and used. If `tiny_dns_cache` is the crate name, it's correct.)*

## Thread Safety

The `Cache` struct itself is **not** internally thread-safe. If you need to share a single cache instance across multiple threads, you must wrap it in appropriate synchronization primitives from the `std::sync` module, such as `Arc<Mutex<Cache>>` or `Arc<RwLock<Cache>>`.

`Arc<RwLock<Cache>>` is often preferred for scenarios where reads are more frequent than writes.

Example:
```rust
use std::sync::{Arc, RwLock};
use tiny_dns_cache::Cache; // Adjust if your crate name is different

fn main() {
    let cache = Arc::new(RwLock::new(Cache::new(Some(1000))));

    // Clone the Arc to share across threads
    let cache_clone1 = Arc::clone(&cache);
    std::thread::spawn(move || {
        // Acquire write lock to put an entry
        let mut writer = cache_clone1.write().unwrap();
        // writer.put(...) // Example: writer.put("example.com", tiny_dns_cache::RecordType::A, vec![], 60);
    });

    let cache_clone2 = Arc::clone(&cache);
    std::thread::spawn(move || {
        // Acquire read lock to get an entry
        let reader = cache_clone2.read().unwrap();
        // reader.get(...) // Example: reader.get("example.com", tiny_dns_cache::RecordType::A);
    });
}
```

## Building and Testing

### Running Tests
To run the unit tests for this library:
```bash
cargo test
```

### Building Documentation
To generate and open the library documentation:
```bash
cargo doc --no-deps --open
```

This will build the documentation for your crate and its dependencies, then open it in your web browser.
The `--no-deps` flag can be used if you only want to build documentation for your crate.

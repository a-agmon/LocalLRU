# LOCAL_LRU

local_lru is a thread-safe and lock-free implementation of LRU (Least Recently Used) caching in Rust.

 Its speed and thread-safety is based on using thread-local storage rather than locking. This means that each thread has its own cache, and the cache is not shared between threads.

 One of the main challenges with LRU caching is that it invovles a lot of writes and updates of its internal data structures: each get and set operation in LRU cache requires updating of at least one pointer.
 This fact diminishes the famous O(1) complexity of LRU cache operations in multithreaded applications, such as web services, which require synchronization and locking mechanisms to ensure thread-safety.

 The thread-local strategy allows us to create a fast, thread-safe, and lock-free O(1) cache, though sacrificing memory. As such, the cache is suitable for applications that require a high-performance and thread-safe cache, but do not require a large memory footprint.

To make a simple example estimation, a web service with 4 cores (4 threads) that caches 1,000,000 strings (each 128 bytes) will require about 1GB of memory. Caching 1M entries of 128 bytes each,
 will require about 250MB of memory. When using LocalCache with 4 cores, the memory footprint will be around 1GB.


## Features

- Thread-safe and lock-free
- High performance with O(1) complexity for cache operations
- Uses thread-local storage for speed and thread-safety
- Includes TTL (Time To Live) expiration

## Example Usage

Here's a basic example of how to use `LocalCache`:
```rust
use local_lru::LocalCache;  
use bytes::Bytes;
let cache = LocalCache::new(2, 60);
cache.add_item("key1".to_string(), Bytes::from("value1"));
assert_eq!(cache.get_item(&"key1".to_string()), Some(Bytes::from("value1")));
```
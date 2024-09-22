//! [`LocalCache`] is a thread safe and lock free implementation of LRU caching.
//! Its speed and thread-safety is based on using thread-local storage rather than locking. This means that each thread has its own cache, and the cache is not shared between threads.
//!
//! One of the main challenges with LRU caching is that it invovles a lot of writings and updates of its internal data structures: each get and set operation in LRU cache requires updating of at least one pointer.
//! This fact diminishes the famous O(1) complexity of LRU cache operations in multithreaded applications, such as web services, which require synchronization and locking mechanisms to ensure thread-safety.
//!
//! The thread-local strategy allows us to create a fast, thread-safe, and lock-free O(1) cache, while sacrificing memory.
//! As such, the cache is suitable for applications that require a high-performance and thread-safe cache, but do not require a large memory footprint.
//! To make a simple example estimation, a web service with 4 cores (4 threads) that caches 1,000,000 strings (each 128 bytes) will require about 1GB of memory. Caching 1M entries of 128 bytes each,
//! will require about 250MB of memory. When using LocalCache with 4 cores, the memory footprint will be around 1GB.
//!
//
//
use bytes::Bytes;
use std::cell::RefCell;

mod cache;
use cache::LRUCache;

thread_local! {
    static CACHE: RefCell<LRUCache> = RefCell::new(LRUCache::new(1, 0));
}

pub struct LocalCache;

impl LocalCache {
    /// Creates a new LocalCache with the given capacity and ttl.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The maximum number of items the cache can hold before evicting the least recently used item.
    /// * `ttl` - The time-to-live for each item in seconds.
    ///
    /// # Example
    ///
    /// ```
    /// use local_lru::LocalCache;  
    /// use bytes::Bytes;
    /// let cache = LocalCache::new(2, 60);
    /// cache.add_item("key1".to_string(), Bytes::from("value1"));
    /// assert_eq!(cache.get_item(&"key1".to_string()), Some(Bytes::from("value1")));
    /// ```
    pub fn new(capacity: usize, ttl: u64) -> Self {
        CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            *cache = LRUCache::new(capacity, ttl);
        });
        LocalCache
    }
    /// Gets an item from the cache. In LRU cache fetching, the item is moved to the front of the list.
    /// # Returns
    ///
    /// An Option containing the item if it exists, or None if it does not.
    pub fn get_item(&self, key: &String) -> Option<Bytes> {
        CACHE.with(|cache| cache.borrow_mut().get_item(key))
    }

    /// Adds an item to the cache.
    /// # Arguments
    ///
    /// * `key` - The key to add the item for.
    /// * `value` - The value to add to the cache represented as `Bytes`.
    ///
    /// # Returns
    ///
    pub fn add_item(&self, key: String, value: Bytes) {
        CACHE.with(|cache| cache.borrow_mut().add_item(key, value))
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::thread::sleep;
    use std::time::Duration;

    #[test]
    fn test_capacity_based_eviction() {
        let cache = LocalCache::new(3, 60);

        cache.add_item("key1".to_string(), Bytes::from("value1"));
        cache.add_item("key2".to_string(), Bytes::from("value2"));
        cache.add_item("key3".to_string(), Bytes::from("value3"));

        assert_eq!(
            cache.get_item(&"key1".to_string()),
            Some(Bytes::from("value1"))
        );
        assert_eq!(
            cache.get_item(&"key2".to_string()),
            Some(Bytes::from("value2"))
        );
        assert_eq!(
            cache.get_item(&"key3".to_string()),
            Some(Bytes::from("value3"))
        );

        // Adding a fourth item should evict the least recently used item (key1)
        cache.add_item("key4".to_string(), Bytes::from("value4"));

        assert_eq!(cache.get_item(&"key1".to_string()), None);
        assert_eq!(
            cache.get_item(&"key2".to_string()),
            Some(Bytes::from("value2"))
        );
        assert_eq!(
            cache.get_item(&"key3".to_string()),
            Some(Bytes::from("value3"))
        );
        assert_eq!(
            cache.get_item(&"key4".to_string()),
            Some(Bytes::from("value4"))
        );
    }

    #[test]
    fn test_get_item_updates_order() {
        let cache = LocalCache::new(3, 60);

        cache.add_item("key1".to_string(), Bytes::from("value1"));
        cache.add_item("key2".to_string(), Bytes::from("value2"));
        cache.add_item("key3".to_string(), Bytes::from("value3"));

        // Access key1, making it the most recently used
        cache.get_item(&"key1".to_string());

        // Add a new item, which should evict the least recently used (now key2)
        cache.add_item("key4".to_string(), Bytes::from("value4"));

        assert_eq!(
            cache.get_item(&"key1".to_string()),
            Some(Bytes::from("value1"))
        );
        assert_eq!(cache.get_item(&"key2".to_string()), None);
        assert_eq!(
            cache.get_item(&"key3".to_string()),
            Some(Bytes::from("value3"))
        );
        assert_eq!(
            cache.get_item(&"key4".to_string()),
            Some(Bytes::from("value4"))
        );
    }

    #[test]
    fn test_ttl_expiration() {
        let cache = LocalCache::new(3, 2); // TTL of 2 seconds

        cache.add_item("key1".to_string(), Bytes::from("value1"));

        assert_eq!(
            cache.get_item(&"key1".to_string()),
            Some(Bytes::from("value1"))
        );

        // Wait for 3 seconds (longer than TTL)
        sleep(Duration::from_secs(3));

        // The item should now be expired
        assert_eq!(cache.get_item(&"key1".to_string()), None);
    }
}

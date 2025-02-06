//! [`LocalCache`] is a thread safe and lock free implementation of LRU caching.
//! Its speed and thread-safety is based on using thread-local storage rather than locking. This means that each thread has its own cache, and the cache is not shared between threads.
//!
//! # Example
//!
//! ```
//! use local_lru::LocalCache;  
//! use bytes::Bytes;
//! // Initialize the cache with a capacity of 2 items and a TTL of 60 seconds
//! let cache = LocalCache::initialize(2, 60);
//! cache.add_item("key1", Bytes::from("value1"));
//! let item = cache.get_item("key1");
//! ```
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
use serde::{de::DeserializeOwned, Serialize};
use std::cell::RefCell;

mod cache;
use cache::LRUCache;

thread_local! {
    static CACHE: RefCell<Option<LRUCache>> = const { RefCell::new(None) };
}

#[derive(Clone)]
pub struct LocalCache {
    capacity: usize,
    ttl: u64,
}

impl LocalCache {
    /// Initilizalizes a new LocalCache with the given capacity and ttl.
    /// Note that this only initializes the parameters that set the cache capacity and ttl.
    /// The cache will be created with the given parameter only when a thread first accesses the cache with call to `get_item` or `add_item`.
    /// Subsequent calls to `initialize` simply modify the cache parameters, which will only effect threads that did not previously access the cache.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The maximum number of items the cache can hold before evicting the least recently used item.
    /// * `ttl` - The time-to-live for each item in seconds. anything less than 1 means no expiration.
    ///
    /// # Example
    ///
    /// ```
    /// use local_lru::LocalCache;  
    /// use bytes::Bytes;
    /// let cache = LocalCache::initialize(2, 60);
    /// cache.add_item("key1", Bytes::from("value1"));
    /// assert_eq!(cache.get_item("key1"), Some(Bytes::from("value1")));
    /// ```
    pub fn initialize(capacity: usize, ttl: u64) -> Self {
        LocalCache { capacity, ttl }
    }

    #[deprecated(since = "0.4.0", note = "Use initialize() instead")]
    pub fn new(capacity: usize, ttl: u64) -> Self {
        LocalCache { capacity, ttl }
    }

    fn initialize_cache_if_none(&self) {
        CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            if cache.is_none() {
                *cache = Some(LRUCache::new(self.capacity, self.ttl));
            }
        });
    }
    /// Gets an item from the cache. In LRU cache fetching, the item is moved to the front of the list.
    /// # Returns
    ///
    /// An Option containing the item if it exists, or None if it does not.
    pub fn get_item(&self, key: &str) -> Option<Bytes> {
        self.initialize_cache_if_none();
        CACHE.with(|cache| {
            if let Some(cache) = cache.borrow_mut().as_mut() {
                cache.get_item(key)
            } else {
                None
            }
        })
    }

    /// Adds an item to the cache.
    /// # Arguments
    ///
    /// * `key` - The key to add the item for.
    /// * `value` - The value to add to the cache represented as `Bytes`.
    ///
    pub fn add_item(&self, key: &str, value: Bytes) {
        self.initialize_cache_if_none();
        CACHE.with(|cache| {
            if let Some(cache) = cache.borrow_mut().as_mut() {
                cache.add_item(key.to_string(), value)
            }
        })
    }

    /// Wrapper function to add a struct to the cache.
    /// It simple uses bincode to serialize the struct and add it to the cache as a Bytes object.
    /// # Arguments
    ///
    /// * `key` - The key to add the item for.
    /// * `value` - Any struct that implements Serialize.
    ///
    pub fn add_struct<T: Serialize>(&self, key: &str, value: T) {
        let bytes = bincode::serialize(&value).unwrap(); // TODO: handle error
        self.add_item(key, Bytes::from(bytes));
    }

    /// Wrapper function to get a struct from the cache.
    /// It uses bincode to deserialize the Bytes object back into a struct.
    /// # Arguments
    ///
    /// * `key` - The key to get the item for.
    ///
    /// # Returns
    ///
    /// An Option containing the item if it exists, or None if it does not.
    pub fn get_struct<T: DeserializeOwned>(&self, key: &str) -> Option<T> {
        let bytes = self.get_item(key)?;
        bincode::deserialize(&bytes).ok()
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;
    use serde::Serialize;
    use std::thread;
    use std::thread::sleep;
    use std::time::Duration;

    #[test]
    fn test_capacity_based_eviction() {
        let cache = LocalCache::initialize(3, 60);

        cache.add_item("key1", Bytes::from("value1"));
        cache.add_item("key2", Bytes::from("value2"));
        cache.add_item("key3", Bytes::from("value3"));

        assert_eq!(cache.get_item("key1"), Some(Bytes::from("value1")));
        assert_eq!(cache.get_item("key2"), Some(Bytes::from("value2")));
        assert_eq!(cache.get_item("key3"), Some(Bytes::from("value3")));

        // Adding a fourth item should evict the least recently used item (key1)
        cache.add_item("key4", Bytes::from("value4"));

        assert_eq!(cache.get_item("key1"), None);
        assert_eq!(cache.get_item("key2"), Some(Bytes::from("value2")));
        assert_eq!(cache.get_item("key3"), Some(Bytes::from("value3")));
        assert_eq!(cache.get_item("key4"), Some(Bytes::from("value4")));
    }

    #[test]
    fn test_get_item_updates_order() {
        let cache = LocalCache::initialize(3, 60);

        cache.add_item("key1", Bytes::from("value1"));
        cache.add_item("key2", Bytes::from("value2"));
        cache.add_item("key3", Bytes::from("value3"));

        // Access key1, making it the most recently used
        cache.get_item("key1");

        // Add a new item, which should evict the least recently used (now key2)
        cache.add_item("key4", Bytes::from("value4"));

        assert_eq!(cache.get_item("key1"), Some(Bytes::from("value1")));
        assert_eq!(cache.get_item("key2"), None);
        assert_eq!(cache.get_item("key3"), Some(Bytes::from("value3")));
        assert_eq!(cache.get_item("key4"), Some(Bytes::from("value4")));
    }

    #[test]
    fn test_ttl_expiration() {
        let cache = LocalCache::initialize(3, 2); // TTL of 2 seconds

        cache.add_item("key1", Bytes::from("value1"));

        assert_eq!(cache.get_item("key1"), Some(Bytes::from("value1")));

        // Wait for 3 seconds (longer than TTL)
        sleep(Duration::from_secs(3));

        // The item should now be expired
        assert_eq!(cache.get_item("key1"), None);
    }

    #[test]
    fn test_no_ttl_expiration() {
        let cache = LocalCache::initialize(3, 0); // TTL of 0 seconds means no expiration

        cache.add_item("key1", Bytes::from("value1"));

        assert_eq!(cache.get_item("key1"), Some(Bytes::from("value1")));

        // Wait for 3 seconds
        sleep(Duration::from_secs(3));

        // The item should still be present as there's no TTL
        assert_eq!(cache.get_item("key1"), Some(Bytes::from("value1")));
    }

    #[test]
    fn test_add_and_get_struct() {
        #[derive(Debug, Serialize, Deserialize, PartialEq, Clone)]
        struct TestStruct {
            field1: String,
            field2: i32,
        }

        let cache = LocalCache::initialize(3, 60);

        let test_struct = TestStruct {
            field1: "Hello".to_string(),
            field2: 42,
        };

        // Add the struct to the cache
        cache.add_struct("test_key", test_struct.clone());

        // Retrieve the struct from the cache
        let retrieved_struct: Option<TestStruct> = cache.get_struct("test_key");

        // Assert that the retrieved struct matches the original
        assert_eq!(retrieved_struct, Some(test_struct.clone()));

        // Test with a non-existent key
        let non_existent: Option<TestStruct> = cache.get_struct("non_existent_key");
        assert_eq!(non_existent, None);
    }

    #[test]
    fn test_thread_local_isolation() {
        let cache = LocalCache::initialize(3, 60);
        let cache_clone = cache.clone(); // Clone for the thread

        // Add item in main thread
        cache.add_item("main_key", Bytes::from("main_value"));

        let thread_handle = thread::spawn(move || {
            cache_clone.get_item("main_key"); // Use clone in thread
            cache_clone.add_item("thread_key", Bytes::from("thread_value"));
        });

        thread_handle.join().unwrap();

        assert_eq!(cache.get_item("main_key"), Some(Bytes::from("main_value")));
        assert_eq!(cache.get_item("thread_key"), None);
    }
}

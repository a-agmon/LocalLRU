# Local LRU

local_lru is a simple, fast, thread-safe and lock-free implementation of LRU (Least Recently Used) caching in Rust. 
Its speed and thread-safety is based on using thread-local storage rather than locking. 

## Features

- Thread-safe and lock-free
- High performance with O(1) complexity for cache operations
- Uses thread-local storage for speed and thread-safety
- Includes TTL (Time To Live) expiration
- Supports adding and retrieving structs

## Example Usage

Here's a basic example of how to use `LocalCache`:
```rust
use local_lru::LocalCache;  
use bytes::Bytes;
// Create a new cache with a capacity of 2 items and a TTL of 60 seconds 
let cache = LocalCache::new(2, 60);
// Create a new cache with a capacity of 2 items and no TTL
let cache = LocalCache::new(2, 0);
// Add an item to the cache
cache.add_item("key1", Bytes::from("value1"));
// Get the item from the cache
assert_eq!(cache.get_item("key1"), Some(Bytes::from("value1")));

// Add a struct to the cache
 #[derive(Debug, Serialize, Deserialize, PartialEq, Clone)]
struct TestStruct {
    field1: String,
    field2: i32,
}
let cache = LocalCache::new(3, 60);
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
```

## Motivation

 One of the main challenges with LRU caching is that it invovles a lot of writes and updates of its internal data structures: each get and set operation in LRU cache requires updating of at least one pointer.
 This fact diminishes the famous O(1) complexity of LRU cache operations in multithreaded applications, such as web services, which require synchronization and locking mechanisms to ensure thread-safety and thus significantly harm performance.

 The thread-local strategy allows us to create a fast, thread-safe, and lock-free O(1) cache for the price of high memory consumption. As such, the cache is suitable for applications that require a high-performance and thread-safe cache, but do not require a large memory footprint.

Using thread-local storage means that each thread has its own cache, and the cache is not shared between threads. This means that a cache item that is added to the cache using one thread will not be accessible to other threads. Users need to be aware of this behavior and design their usage of the cache accordingly. This can be very useful to applications that cache results of database queries, for example. If your app has 4 cores, then it will have 4 caches, one per core, and for each row you will have to access the database at most 4 times, once per core. But you will gain in performance and scalability, avoiding locks and mutexes.

## Example using local_lru in an Axum service for caching

 ```rust
 struct CacheItem {
    key: String,
    value: String,
}
#[tokio::main]
async fn main() {
    let cache = Arc::new(LocalCache::new(100, 120));
    let app = axum::Router::new()
        .route("/get/:key", axum::routing::get(get_key))
        .route("/post", axum::routing::post(post_key))
        .with_state(cache);

    let listener = TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

async fn get_key(
    State(cache): State<Arc<LocalCache>>,
    Path(key): Path<String>,
) -> (StatusCode, String) {
    if let Some(content) = cache.get_item(&key) {
        let content_str = String::from_utf8(content.to_vec()).unwrap();
        let response_str = format!(
            "{{ \"key\": \"{}\", \"value\": \"{}\" }}",
            key, content_str
        );
        (StatusCode::OK, response_str)
    } else {
        (StatusCode::NOT_FOUND, "".to_string())
    }
}
 ```


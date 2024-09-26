use bytes::Bytes;
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::{Rc, Weak};
use std::time::SystemTime;

#[derive(PartialEq, Clone, Copy)]
pub enum CacheItemTTL {
    ExpiresAt(u64),
    Persist,
}

pub(crate) struct CacheItem<V> {
    key: String,
    value: V,
    expires_at: CacheItemTTL,
    prev: Option<Weak<RefCell<CacheItem<V>>>>,
    next: Option<Rc<RefCell<CacheItem<V>>>>,
}

pub(crate) struct LRUCache<V> {
    capacity: usize,
    ttl: u64,
    map: HashMap<String, Rc<RefCell<CacheItem<V>>>>,
    head: Option<Rc<RefCell<CacheItem<V>>>>,
    tail: Option<Rc<RefCell<CacheItem<V>>>>,
}

impl<V: Clone> LRUCache<V> {
    pub(crate) fn new(capacity: usize, ttl_seconds: u64) -> Self {
        LRUCache {
            capacity,
            ttl: ttl_seconds,
            map: HashMap::new(),
            head: None,
            tail: None,
        }
    }

    /// Adds an item to the cache. If the item already exists, it updates the value and moves it to the front.
    /// If adding the new item exceeds the capacity, it removes the least recently used item.
    pub(crate) fn add_item(&mut self, key: String, value: V) {
        if let Some(node) = self.map.get(&key) {
            // Update the value and move the node to the head.
            node.borrow_mut().value = value.clone();
            self.move_to_head(Rc::clone(node));
        } else {
            // Create a new node.
            let new_node = self.create_node(key.clone(), value);
            // Add the new node to the front and insert it into the map.
            self.add_to_head(Rc::clone(&new_node));
            self.map.insert(key.clone(), Rc::clone(&new_node));

            // If capacity is exceeded, remove the least recently used item.
            if self.map.len() > self.capacity {
                if let Some(tail_node) = self.tail.take() {
                    let tail_key = tail_node.borrow().key.clone();
                    self.remove_node(Rc::clone(&tail_node));
                    self.map.remove(&tail_key);
                }
            }
        }
    }

    /// Retrieves an item from the cache by key. If the item exists, it moves it to the front.
    pub(crate) fn get_item(&mut self, key: &str) -> Option<V> {
        let node = self.map.get(key)?;
        // Extract node props in a scope of an immutable borrow
        let (value, expires_at) = {
            let node_borrow = node.borrow();
            (node_borrow.value.clone(), node_borrow.expires_at)
        };
        match expires_at {
            CacheItemTTL::Persist => {
                self.move_to_head(Rc::clone(node));
                Some(value)
            }
            CacheItemTTL::ExpiresAt(expires_at) if self.now_seconds() > expires_at => {
                self.remove_node(Rc::clone(node));
                self.map.remove(key);
                None
            }
            CacheItemTTL::ExpiresAt(_) => {
                self.move_to_head(Rc::clone(node));
                Some(value)
            }
        }
    }

    /// Moves the given node to the front of the list.
    fn move_to_head(&mut self, node: Rc<RefCell<CacheItem<V>>>) {
        self.remove_node(Rc::clone(&node));
        self.add_to_head(node);
    }

    /// Removes the given node from the list.
    fn remove_node(&mut self, node: Rc<RefCell<CacheItem<V>>>) {
        let prev_weak = node.borrow_mut().prev.take();
        let next_opt = node.borrow_mut().next.take();

        if let Some(ref prev_weak_ref) = prev_weak {
            if let Some(prev_rc) = prev_weak_ref.upgrade() {
                prev_rc.borrow_mut().next = next_opt.clone();
            }
        } else {
            // Node is head
            self.head = next_opt.clone();
        }

        if let Some(next_rc) = next_opt {
            next_rc.borrow_mut().prev = prev_weak.clone();
        } else {
            // Node is tail
            if let Some(ref prev_weak_ref) = prev_weak {
                self.tail = prev_weak_ref.upgrade();
            } else {
                // List is empty
                self.tail = None;
            }
        }
    }

    /// Adds the given node to the front of the list.
    fn add_to_head(&mut self, node: Rc<RefCell<CacheItem<V>>>) {
        node.borrow_mut().prev = None;
        node.borrow_mut().next = self.head.clone();

        if let Some(old_head) = &self.head {
            old_head.borrow_mut().prev = Some(Rc::downgrade(&node));
        } else {
            // List was empty, so tail is also node
            self.tail = Some(Rc::clone(&node));
        }

        self.head = Some(node);
    }

    fn now_seconds(&self) -> u64 {
        SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs()
    }
    fn create_node(&self, key: String, value: V) -> Rc<RefCell<CacheItem<V>>> {
        let expires_at = if self.ttl < 1 {
            CacheItemTTL::Persist
        } else {
            CacheItemTTL::ExpiresAt(self.now_seconds() + self.ttl)
        };
        Rc::new(RefCell::new(CacheItem {
            key: key.clone(),
            value: value.clone(),
            expires_at,
            prev: None,
            next: None,
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_with_int() {
        let mut cache = LRUCache::<i32>::new(2, 60);
        cache.add_item("one".to_string(), 1);
        cache.add_item("two".to_string(), 2);

        assert_eq!(cache.get_item("one"), Some(1));
        assert_eq!(cache.get_item("two"), Some(2));

        // Add a third item, which should evict the least recently used item ("two")
        cache.add_item("three".to_string(), 3);

        assert_eq!(cache.get_item("one"), None);
        assert_eq!(cache.get_item("two"), Some(2));
        assert_eq!(cache.get_item("three"), Some(3));
    }

    #[test]
    fn test_cache_with_string() {
        let mut cache = LRUCache::<String>::new(2, 60);
        cache.add_item("key1".to_string(), "value1".to_string());
        cache.add_item("key2".to_string(), "value2".to_string());

        assert_eq!(cache.get_item("key1"), Some("value1".to_string()));
        assert_eq!(cache.get_item("key2"), Some("value2".to_string()));

        // Update an existing item
        cache.add_item("key1".to_string(), "new_value1".to_string());

        assert_eq!(cache.get_item("key1"), Some("new_value1".to_string()));
        assert_eq!(cache.get_item("key2"), Some("value2".to_string()));
    }
}

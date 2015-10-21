use std::collections::HashMap;

#[derive(Clone)]
pub struct IndexHeap<T> {
    elements: Vec<T>,
    indices: HashMap<usize, usize>,
    reverse: Vec<usize>,
    size: usize
}

impl <T: PartialOrd> IndexHeap<T> {
    pub fn new() -> IndexHeap<T> {
        IndexHeap{ elements: Vec::new(), indices: HashMap::new(), reverse: Vec::new(), size: 0 }
    }

    pub fn empty(&self) -> bool {
        self.size == 0
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn top(&self) -> Option<&T> {
        if self.empty() {
            None
        } else {
            Some(&self.elements[0])
        }
    }

    pub fn contains_index(&self, index: usize) -> bool {
        self.indices.contains_key(&index)
    }

    pub fn into_vec(self) -> Vec<T> { self.elements }

    pub fn into_indices_vec(&self) -> Vec<usize> {
        self.indices.keys().map(|&x| x).collect()
    }

    pub fn push(&mut self, index: usize, item: T) {
        let size = self.size;

        self.elements.push(item);
        self.reverse.push(index);
        self.indices.insert(index, size);
        self.bubble_up(size);
        self.size += 1;
    }

    pub fn push_without_index(&mut self, item: T) {
        let size = self.size;
        self.push(size, item);
    }

    pub fn pop(&mut self) -> Option<T> {
        if self.empty() {
            None
        } else {
            let index = self.size - 1;
            self.swap(0, index);

            let result = self.elements.pop();
            self.size -= 1;
            self.bubble_down(0);

            self.indices.remove(&self.reverse[self.size]);
            self.reverse.pop();

            result
        }
    }

    pub fn update(&mut self, index: usize, item: T) {
        match self.indices.get(&index) {
            Some(&i) => {
                self.elements[i] = item;
                self.bubble_down(i);
                self.bubble_up(i);
            },
            None => self.push(index, item)  // index not present, insert item at given index
        }
    }

}

impl <T: PartialOrd> IndexHeap<T> {
    fn bubble_up(&mut self, mut index: usize) {
        loop {
            if index == 0 { break; }

            let parent_index = parent(index);

            if self.elements[index] >= self.elements[parent_index] {
                break;
            }

            self.swap(index, parent_index);
            index = parent_index;
        }
    }

    fn bubble_down(&mut self, mut index: usize) {
        loop {
            let left_index = left(index);
            let right_index = right(index);
            let mut next_index = left_index;

            if !self.in_bounds(next_index) {
                break;
            } else if self.in_bounds(right_index) && self.elements[right_index] < self.elements[next_index] {
                next_index = right_index;
            }

            if self.elements[next_index] >= self.elements[index] {
                break;
            }

            self.swap(index, next_index);
            index = next_index;
        }
    }

    fn swap(&mut self, i: usize, j: usize) {
        self.elements.swap(i, j);

        let tmp = self.reverse[i];
        self.reverse[i] = self.reverse[j];
        self.reverse[j] = tmp;

        self.indices.insert(self.reverse[i], i);
        self.indices.insert(self.reverse[j], j);
    }

    fn in_bounds(&self, index: usize) -> bool {
        index < self.size
    }
}

fn left(index: usize) -> usize {
    (index << 1) + 1
}

fn right(index: usize) -> usize {
    (index << 1) + 2
}

fn parent(index: usize) -> usize {
    (index - 1) >> 1
}

#[cfg(test)]
mod test {
    use super::IndexHeap;

    use std::cmp::Ordering;
    use std::usize;

    #[test]
    fn small() {
        let mut heap = IndexHeap::new();

        heap.push_without_index(42);
        heap.push_without_index(90);

        match heap.pop() {
            Some(x) => assert_eq!(42, x),
            None => assert!(false)
        }

        match heap.pop() {
            Some(x) => assert_eq!(90, x),
            None => assert!(false)
        }

        assert!(heap.pop().is_none());
    }

    #[test]
    fn heapsort() {
        let v: Vec<i32> = vec![10, 12, 1, 42, 8, 19, 99, 0];
        let mut w = v.clone();
        let mut heap = IndexHeap::new();

        for x in &v {
            heap.push_without_index(x);
        }

        let mut u: Vec<i32> = Vec::new();

        while let Some(x) = heap.pop() {
            u.push(*x);
        }

        w.sort();

        assert_eq!(w, u);
    }

    #[test]
    fn update() {
        let items: Vec<i32> = vec![10, 42, 35];
        let mut heap: IndexHeap<i32> = IndexHeap::new();

        // heap will contain (0, 10), (2, 35), (1, 42)
        for (i, item) in items.iter().enumerate() {
            heap.push(i, *item);
        }

        // heap will contain (2, 0), (0, 10), (1, 42)
        heap.update(2, 0);

        match heap.top() {
            Some(&x) => assert_eq!(0, x),
            None => assert!(false)
        }
    }

    #[test]
    fn size() {
        let mut heap = IndexHeap::new();

        heap.push(0, 10);
        heap.push(1, 42);
        heap.push(2, 35);

        assert_eq!(3, heap.size());

        heap.pop();

        assert_eq!(2, heap.size());

        heap.pop();
        heap.pop();
        heap.pop();

        assert_eq!(0, heap.size());
    }

    #[test]
    fn into_vec() {
        let mut heap = IndexHeap::new();

        heap.push(0, 10);
        heap.push(1, 42);
        heap.push(2, 35);

        let mut v = heap.into_vec();
        v.sort();

        assert_eq!(vec![10, 35, 42], v);
    }

    #[test]
    fn into_indices_vec() {
        let mut heap = IndexHeap::new();

        heap.push(0, 10);
        heap.push(1, 42);
        heap.push(2, 35);

        let mut indices = heap.into_indices_vec();
        indices.sort();

        assert_eq!(vec![0, 1, 2], indices);
    }

    #[test]
    fn contains() {
        let mut heap = IndexHeap::new();

        heap.push(0, 10);
        heap.push(1, 42);
        heap.push(2, 35);

        assert!(heap.contains_index(0));
        assert!(!heap.contains_index(5));
    }

    #[test]
    fn partial_ord() {
        let mut heap = IndexHeap::new();

        heap.push_without_index(42.0);
        heap.push_without_index(3.14);
        heap.push_without_index(2.71);

        assert_eq!(2.71, heap.pop().unwrap());
        assert_eq!(3.14, heap.pop().unwrap());
        assert_eq!(42.0, heap.pop().unwrap());
    }

    #[test]
    fn dijkstra() {
        #[derive(Copy, Clone, Eq, PartialEq)]
        struct State {
            cost: usize,
            position: usize,
        }

        impl Ord for State {
            fn cmp(&self, other: &State) -> Ordering {
                self.cost.cmp(&other.cost)
            }
        }

        impl PartialOrd for State {
            fn partial_cmp(&self, other: &State) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }

        struct Edge {
            node: usize,
            cost: usize,
        }

        fn shortest_path(adj_list: &Vec<Vec<Edge>>, start: usize, goal: usize) -> usize {
            let mut dist: Vec<_> = (0..adj_list.len()).map(|_| usize::MAX).collect();

            let mut heap = IndexHeap::new();

            dist[start] = 0;
            heap.push(start, State { cost: 0, position: start });

            while let Some(State { cost, position }) = heap.pop() {
                if position == goal { return cost; }
                if cost > dist[position] { continue; }

                for edge in &adj_list[position] {
                    let next = State { cost: cost + edge.cost, position: edge.node };

                    if next.cost < dist[next.position] {
                        heap.update(next.position, next);
                        dist[next.position] = next.cost;
                    }
                }
            }

            usize::MAX
        }

        let graph = vec![
            // Node 0
            vec![Edge { node: 2, cost: 10 },
                 Edge { node: 1, cost: 1 }],
            // Node 1
            vec![Edge { node: 3, cost: 2 }],
            // Node 2
            vec![Edge { node: 1, cost: 1 },
                 Edge { node: 3, cost: 3 },
                 Edge { node: 4, cost: 1 }],
            // Node 3
            vec![Edge { node: 0, cost: 7 },
                 Edge { node: 4, cost: 2 }],
            // Node 4
            vec![]
        ];

        assert_eq!(shortest_path(&graph, 0, 1), 1);
        assert_eq!(shortest_path(&graph, 0, 3), 3);
        assert_eq!(shortest_path(&graph, 3, 0), 7);
        assert_eq!(shortest_path(&graph, 0, 4), 5);
        assert_eq!(shortest_path(&graph, 4, 0), usize::MAX);
    }
}

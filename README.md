# graphs

Represent and manipulate graphs efficiently and easily

## Quickstart

Add this line bellow `[dependencies]` in your `Cargo.toml` file:
```
graphs = { git = "https://github.com/TiagoCavalcante/graphs", tag = "0.3.2" }
```

And to create a graph:
```rs
use graphs::Graph;

let size = 10_100;
let density = 0.1;
let mut graph = Graph::new(size);
graph.fill(size);
```

Here is an implementation of the
[BFS](https://en.wikipedia.org/wiki/Breadth-first_search)
algorithm:
```rs
use graphs::Graph;

fn bfs(
  graph: &Graph,
  start: usize,
  end: usize,
) -> Option<Vec<usize>> {
  let mut queue = std::collections::VecDeque::new();

  let mut distance = vec![usize::MAX; graph.size];
  let mut predecessor = vec![usize::MAX; graph.size];

  distance[start] = 0;

  queue.push_back(start);

  while let Some(current) = queue.pop_front() {
    for &vertex in graph.get_neighbors(current) {
      if distance[vertex] == usize::MAX {
        distance[vertex] = distance[current] + 1;
        predecessor[vertex] = current;
        queue.push_back(vertex);

        if vertex == end {
          let mut path = vec![end];
          let mut current = end;
          while predecessor[current] != usize::MAX {
            current = predecessor[current];
            path.push(current);
          }

          path.reverse();

          return Some(path);
        }
      }
    }
  }

  return None;
}
```

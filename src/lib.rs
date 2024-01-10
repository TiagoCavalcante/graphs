//! Represent and manipulate graphs efficiently and easily
//!
//! # Quick start
//!
//! Add these lines bellow `[dependencies]` in your
//! `Cargo.toml` file:
//! ```toml
//! graphs = {
//!   git = "https://github.com/TiagoCavalcante/graphs",
//!   tag = "0.3.2"
//! }
//! ```
//!
//! With [graphs](https://github.com/TiagoCavalcante/graphs)
//! it is super easy to create and fill graphs:
//! ```
//! use graphs::Graph;
//!
//! let density = 0.1;
//! let size = 1000;
//! let mut graph = Graph::new(size);
//! graph.fill(density);
//! ```
//!
//! Here is an implementation of the
//! [BFS](https://en.wikipedia.org/wiki/Breadth-first_search)
//! algorithm:
//! ```
//! use graphs::Graph;
//!
//! fn bfs(
//!   graph: &Graph,
//!   start: usize,
//!   end: usize,
//! ) -> Option<Vec<usize>> {
//!   let mut queue = std::collections::VecDeque::new();
//!
//!   let mut distance = vec![usize::MAX; graph.size];
//!   let mut predecessor = vec![usize::MAX; graph.size];
//!
//!   distance[start] = 0;
//!
//!   queue.push_back(start);
//!
//!   while let Some(current) = queue.pop_front() {
//!     for &vertex in graph.get_neighbors(current) {
//!       if distance[vertex] == usize::MAX {
//!         distance[vertex] = distance[current] + 1;
//!         predecessor[vertex] = current;
//!         queue.push_back(vertex);
//!
//!         if vertex == end {
//!           let mut path = vec![end];
//!           let mut current = end;
//!           while predecessor[current] != usize::MAX {
//!             current = predecessor[current];
//!             path.push(current);
//!           }
//!
//!           path.reverse();
//!
//!           return Some(path);
//!         }
//!       }
//!     }
//!   }
//!
//!   return None;
//! }
//! ```
//!
//! You will find more examples and fuctions in [Graph].

#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(rustdoc::missing_crate_level_docs)]
#![deny(rustdoc::invalid_codeblock_attributes)]
#![deny(rustdoc::invalid_html_tags)]
#![deny(rustdoc::invalid_rust_codeblocks)]
#![deny(rustdoc::bare_urls)]

#[doc = include_str!("../README.md")]

mod rand;
mod unweighted;
mod weighted;

pub use self::unweighted::Graph;
pub use self::weighted::WeightedGraph;

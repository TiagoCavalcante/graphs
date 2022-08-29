//! WeightedGraph struct and implementation.
//!
//! Differently from unweighted graphs, weighted graphs
//! don't have functions for undirected graphs.
//!
//! Some functions like `get_neighbors` could have better
//! names for weighted graphs, but to keep compatibility
//! with unweighted graphs the names are kept.

use super::rand::{BoolRng, NormalRng, UniformRng};

use std::fs::File;
use std::io::{BufRead, BufReader, Write};

/// A weighted graph represented using an
/// [adjacency list](https://en.wikipedia.org/wiki/Adjacency_list).
/// ```
/// use graphs::WeightedGraph;
///
/// // I told you, fast and easy.
/// const size: usize = 1_000;
/// let graph = WeightedGraph::<size>::new();
/// ```
pub struct WeightedGraph<const N: usize> {
  /// The number of vertices in the graph.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// const size: usize = 10_000;
  /// let graph = WeightedGraph::<size>::new();
  /// assert_eq!(graph.size, size);
  /// ```
  pub size: usize,
  /// The adjacency list, you should not use this directly,
  /// if you want to get the neighbors of a vertex use
  /// [WeightedGraph::get_neighbors] instead.
  /// The 1st element is the neighbor number and the 2nd is
  /// the weight.
  data: [Vec<(usize, f32)>; N],
}

impl<const N: usize> WeightedGraph<N> {
  /// Add an edge between the vertices `a` and `b`.
  ///
  /// This is undefined behaviour if already there is an
  /// edge between `a` and `b`, so if you are not sure if
  /// this edge already exists you should use
  /// [WeightedGraph::has_edge].
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  ///
  /// graph.fill(0.8, 3.5, 6.28);
  ///
  /// // We want to ensure that there is an edge between the
  /// // vertex 0 and the vertex 1.
  /// if !graph.has_edge(0, 1) {
  ///   graph.add_edge(0, 1, 9.9);
  /// }
  /// ```
  ///
  /// This is undefined behaviour in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [Graph::add_edge_undirected] instead.
  pub fn add_edge(
    &mut self,
    a: usize,
    b: usize,
    weight: f32,
  ) {
    self.data[a].push((b, weight));
  }

  /// Add an edge between the vertices `a` and `b`.
  ///
  /// This is undefined behaviour if already there is an
  /// edge between `a` and `b`, so if you are not sure if
  /// this edge already exists you should use
  /// [Graph::has_edge].
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  ///
  /// graph.fill_undirected(0.8, 1.0, 0.1);
  ///
  /// // We want to ensure that there is an edge between the
  /// // vertex 0 and the vertex 1.
  /// if !graph.has_edge(0, 1) {
  ///   graph.add_edge_undirected(0, 1, 0.5);
  /// }
  /// ```
  ///
  /// This is undefined behaviour in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [Graph::add_edge] instead.
  pub fn add_edge_undirected(
    &mut self,
    a: usize,
    b: usize,
    weight: f32,
  ) {
    self.data[a].push((b, weight));
    self.data[b].push((a, weight));
  }

  /// Remove the edge from `a` to `b` in a graph.
  /// This is undefined behaviour if there isn't an edge
  /// between `a` and `b`, so if you are not sure if this
  /// edge exists you should use [WeightedGraph::has_edge].
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  /// graph.fill(0.7, 0.2, 3.2);
  ///
  /// // We don't want an edge between 0 and 9, we are not
  /// // sure it it exists, so we check it it exists, and
  /// // if it does, we remove it.
  /// if graph.has_edge(0, 9) {
  ///   graph.remove_edge(0, 9);
  /// }
  /// ```
  pub fn remove_edge(&mut self, a: usize, b: usize) {
    let b_position = self.data[a]
      .iter()
      .position(|&(v, _)| v == b)
      .unwrap();
    // Remove b from a.
    self.data[a].swap_remove(b_position);
  }

  /// Returns whether there is an edge between the vertices
  /// `a` and `b`.
  ///
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  /// graph.fill(0.1, 1.1, 25.0);
  ///
  /// if graph.has_edge(0, 1) {
  ///   println!("We are lukcy!");
  /// }
  /// ```
  ///
  /// This is slow and should be replaced with a loop over
  /// the neighbors everywhere it is possible.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  /// graph.fill(0.5, 0.05, 1100.0);
  ///
  /// let vertex = 5;
  ///
  /// // Avoid this.
  /// for other in 0..graph.size {
  ///   if graph.has_edge(vertex, other) {
  ///     println!("{vertex} -> {other}");
  ///   }
  /// }
  /// // Use this instead.
  /// for &(neighbor, _) in graph.get_neighbors(vertex) {
  ///   println!("{vertex} -> {neighbor}");
  /// }
  /// ```
  pub fn has_edge(&self, a: usize, b: usize) -> bool {
    self.data[a].iter().any(|&(neighbor, _)| neighbor == b)
  }

  /// Retunrs the cost of the edge from `a` to `b`, or
  /// `None` if the edge doesn't exist.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<2>::new();
  /// graph.add_edge(0, 1, 55.0);
  ///
  /// assert_eq!(graph.get_edge(0, 1), Some(55.0));
  /// assert_eq!(graph.get_edge(1, 0), None);
  /// ```
  pub fn get_edge(
    &self,
    a: usize,
    b: usize,
  ) -> Option<f32> {
    self.data[a]
      .iter()
      .find(|(neighbor, _)| *neighbor == b)
      .map(|&(_, cost)| cost)
  }

  /// Add edges between `vertex` and each neighbor of
  /// `neighbors`, it is usually used in conjunction with
  /// `pop_edges`.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// fn shortest_path<const N: usize>(
  ///  graph: &WeightedGraph<N>,
  ///  start: usize,
  ///  end: usize,
  ///) -> Option<Vec<usize>> {
  ///  let mut queue = std::collections::VecDeque::new();
  ///
  ///  let mut distance = vec![usize::MAX; graph.size];
  ///  let mut predecessor = vec![usize::MAX; graph.size];
  ///
  ///  distance[start] = 0;
  ///
  ///  queue.push_back(start);
  ///
  ///  while let Some(current) = queue.pop_front() {
  ///    for &(vertex, _) in graph.get_neighbors(current) {
  ///      if distance[vertex] == usize::MAX {
  ///        distance[vertex] = distance[current] + 1;
  ///        predecessor[vertex] = current;
  ///        queue.push_back(vertex);
  ///
  ///        if vertex == end {
  ///          let mut path = vec![end];
  ///          let mut current = end;
  ///          while predecessor[current] != usize::MAX {
  ///            current = predecessor[current];
  ///            path.push(current);
  ///          }
  ///
  ///          path.reverse();
  ///
  ///          return Some(path);
  ///        }
  ///      }
  ///    }
  ///  }
  ///
  ///  return None;
  ///}
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  /// graph.fill(0.3, 3.0, 6.8);
  ///
  /// let vertex = 5;
  /// let start = 0;
  /// let end = 9;
  ///
  /// let neighbors = graph.pop_edges(vertex);
  /// let path_without_vertex =
  ///   shortest_path(&graph, start, end);
  /// // Restore the edges.
  /// graph.add_edges(vertex, &neighbors);
  /// ```
  pub fn add_edges(
    &mut self,
    vertex: usize,
    neighbors: &Vec<(usize, f32)>,
  ) {
    for &(neighbor, weight) in neighbors {
      self.add_edge(vertex, neighbor, weight);
    }
  }

  /// Returns the neighbors of `vertex` and remove the edges
  /// between `vertex` and its neighbors.
  /// This may be useful in alorithms like
  /// [k-th shortest path](https://en.wikipedia.org/wiki/Yen's_algorithm).
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<50>::new();
  /// graph.fill(1.0, 0.1, 1.0);
  ///
  /// // Pop the edges of all even vertices.
  /// for vertex in (0..50).step_by(2) {
  ///   graph.pop_edges(vertex);
  /// }
  /// ```
  pub fn pop_edges(
    &mut self,
    vertex: usize,
  ) -> Vec<(usize, f32)> {
    let neighbors = self.data[vertex].clone();

    self.data[vertex].clear();

    neighbors
  }

  /// Returns the neighbors of a vertex.
  /// As the graph is represented using an
  /// [adjacency list](https://en.wikipedia.org/wiki/Adjacency_list)
  /// this is an instantaneous operation, and is going to be
  /// inlined.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<1_000>::new();
  /// graph.fill_until(0.1, 0.7, 3.14);
  ///
  /// // This whole loop is going to be striped out when
  /// // compiling with --release.
  /// for vertex in 0..graph.size {
  ///   graph.get_neighbors(vertex);
  /// }
  /// ```
  pub const fn get_neighbors(
    &self,
    vertex: usize,
  ) -> &Vec<(usize, f32)> {
    &self.data[vertex]
  }

  /// Returns the maximum "density" of the graph, that is,
  /// the maximum number of real edges over the maximum
  /// number of real edges plus the number of edges from a
  /// vertex to itself.
  ///
  /// If you want to calculate the density of the graph use
  /// [WeightedGraph::density] instead.
  ///
  /// For example:
  /// The
  /// [matrix representation](https://en.wikipedia.org/wiki/Adjacency_matrix)
  /// of a [complete graph](https://en.wikipedia.org/wiki/Complete_graph)
  /// with 4 vertices is the following:
  /// <table>
  ///   <tr>
  ///     <td>0</td>
  ///     <td>1</td>
  ///     <td>1</td>
  ///     <td>1</td>
  ///   </tr>
  ///   <tr>
  ///     <td>1</td>
  ///     <td>0</td>
  ///     <td>1</td>
  ///     <td>1</td>
  ///   </tr>
  ///   <tr>
  ///     <td>1</td>
  ///     <td>1</td>
  ///     <td>0</td>
  ///     <td>1</td>
  ///   </tr>
  ///   <tr>
  ///     <td>1</td>
  ///     <td>1</td>
  ///     <td>1</td>
  ///     <td>0</td>
  ///   </tr>
  /// </table>
  /// The ones represent that there is an edge between the
  /// vertex with the number of the column and the vertex
  /// with the number of the row.
  /// The zeros represent that there isn't an edge, in this
  /// case, between a vertex and itself.
  /// This function returns the number of ones over the size
  /// of the matrix representation.
  /// This is only meaningful for small graphs as the
  /// maximum "density" converges to one in big graphs.
  /// If you didn't understant what this function does,
  /// don't worry, you aren't really supposed to use this.
  ///
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<100>::new();
  /// graph.fill(1.0, 0.5, 3.2);
  ///
  /// assert!(graph.max_data_density() < graph.density());
  /// ```
  pub fn max_data_density(&self) -> f32 {
    (self.size - 1) as f32 / self.size as f32
  }

  /// Returns the maximum number of edges in a graph.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let graph = WeightedGraph::<3>::new();
  /// // The possible edges are:
  /// // 0 -> 1
  /// // 0 -> 2
  /// // 1 -> 0
  /// // 1 -> 2
  /// // 2 -> 0
  /// // 2 -> 1
  /// assert_eq!(graph.max_number_of_edges(), 6);
  /// ```
  pub const fn max_number_of_edges(&self) -> usize {
    self.size * (self.size - 1)
  }

  /// Returns the density of a graph, that is, the ratio
  /// between the number of edges and the maximum number of
  /// possible edges.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<1_000>::new();
  /// graph.fill_until(0.1, 0.9, 1.1);
  ///
  /// let density = graph.density();
  /// assert!(0.09 < density && density < 0.11);
  ///
  /// graph.clear();
  ///
  /// graph.fill(0.1, 10.0, 9.9);
  ///
  /// let density = graph.density();
  /// assert!(0.09 < density && density < 0.11);
  /// ```
  pub fn density(&self) -> f32 {
    let mut edges = 0;

    for neighbors in &self.data {
      edges += neighbors.len();
    }

    edges as f32 / self.max_number_of_edges() as f32
  }

  /// Randomly add positive weighted edges to the graph
  /// until it reaches the desired density.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  /// graph.fill(1.0, 0.3, 6.7);
  ///
  /// assert!(graph.has_edge(0, 9));
  /// ```
  ///
  /// If you want to do this in a graph that already have
  /// edges you need to use
  /// [WeightedGraph::fill_until] instead.
  ///
  /// [WeightedGraph::fill_until] is faster for sparse graphs.
  ///
  /// This is undefined behaviour in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [Graph::fill_undirected] instead.
  pub fn fill(
    &mut self,
    density: f32,
    mean: f32,
    std_dev: f32,
  ) {
    let real_density = density / self.max_data_density();

    let mut edge_rng = BoolRng::new(real_density);
    let mut weight_rng = NormalRng::new(mean, std_dev);

    for i in 0..self.size {
      for j in 0..self.size {
        // This ensures we don't add edges between an vertex
        // and itself.
        if i != j {
          if edge_rng.sample() {
            self.add_edge(i, j, weight_rng.sample());
          }
        }
      }
    }
  }

  /// Randomly add edges to the graph until it reaches the
  /// desired density.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  /// graph.fill_undirected(1.0, 1.0, 0.1);
  ///
  /// assert!(graph.has_edge(0, 9));
  /// assert!(graph.has_edge(9, 0));
  /// ```
  /// If you want to do this in a graph that already have
  /// edges you need to use
  /// [Graph::fill_until_undirected] instead.
  ///
  /// [Graph::fill_until_undirected] is faster for sparse
  /// graphs.
  ///
  /// This is undefined behaviour in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [Graph::fill] instead.
  pub fn fill_undirected(
    &mut self,
    density: f32,
    mean: f32,
    std_dev: f32,
  ) {
    let real_density = density / self.max_data_density();

    let mut edge_rng = BoolRng::new(real_density);
    let mut weight_rng = NormalRng::new(mean, std_dev);

    for i in 0..self.size {
      for j in 0..self.size {
        // This ensures we don't add edges between an vertex
        // and itself.
        if i < j {
          if edge_rng.sample() {
            self.add_edge_undirected(
              i,
              j,
              weight_rng.sample(),
            );
          }
        }
      }
    }
  }

  /// Randomly add positive weighted edges to the graph
  /// until it reaches the desired density.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  ///
  /// graph.add_edge(0, 1, 1.0);
  /// graph.add_edge(1, 2, 1.0);
  /// graph.add_edge(2, 3, 1.0);
  ///
  /// assert!(!graph.has_edge(0, 9));
  ///
  /// unsafe {
  ///   graph.fill_until(0.3, 0.25, 8.4);
  /// }
  ///
  /// let density = graph.density();
  ///
  /// assert!(0.2 < density && density < 0.4);
  /// ```
  /// Expect this to run forever for any density above 0.7.
  ///
  /// [WeightedGraph::fill] is faster for dense graphs, but only
  /// works with empty graphs.
  pub fn fill_until(
    &mut self,
    density: f32,
    mean: f32,
    std_dev: f32,
  ) {
    let real_density = density - self.density();

    let mut remaining_edges = (real_density
      // This is squared because we need to "throw the coin"
      // for each pair of vertices.
      * self.size.pow(2) as f32)
      as usize;

    let mut vertex_rng = UniformRng::new(0, self.size);
    let mut weight_rng = NormalRng::new(mean, std_dev);

    while remaining_edges != 0 {
      let a = vertex_rng.sample();
      let b = vertex_rng.sample();

      if a != b && !self.has_edge(a, b) {
        self.add_edge(a, b, weight_rng.sample());

        remaining_edges -= 1;
      }
    }
  }

  /// Remove all edges from the graph.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  /// graph.fill(1.0, 2.0, 7.8);
  ///
  /// graph.clear();
  ///
  /// assert_eq!(graph.density(), 0.0);
  /// ```
  pub fn clear(&mut self) {
    for neighbors in &mut self.data {
      neighbors.clear();
    }
  }

  /// Load the graph from `path`.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<100>::new();
  /// match graph.load("graph.grs") {
  ///   Ok(_) => println!("Success!"),
  ///   Err(_) => println!("An error occurred"),
  /// }
  /// ```
  pub fn load(
    &mut self,
    path: &str,
  ) -> std::io::Result<()> {
    let file = File::open(path)?;

    for line in BufReader::new(file).lines() {
      let line = line?;
      let edge =
        line.split_whitespace().collect::<Vec<_>>();

      let a = edge[0].parse().unwrap();
      let b = edge[1].parse().unwrap();
      let weight = edge[2].parse().unwrap();

      self.add_edge(a, b, weight);
    }

    Ok(())
  }

  /// Save the graph to `path`.
  /// ```no_run
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph1 = WeightedGraph::<100>::new();
  ///
  /// graph1.fill(0.3, 0.1, 5.0);
  ///
  /// graph1.save("./graphs.grs");
  ///
  /// let mut graph2 = WeightedGraph::<100>::new();
  ///
  /// match graph2.load("./graph.grs") {
  ///   Ok(_) => println!("Success!"),
  ///   Err(_) => panic!("An error occurred"),
  /// }
  /// ```
  pub fn save(&self, path: &str) -> std::io::Result<()> {
    let mut file = File::create(path)?;

    for vertex in 0..self.size {
      for &(neighbor, weight) in self.get_neighbors(vertex)
      {
        file.write(
          format!("{} {} {}\n", vertex, neighbor, weight)
            .as_bytes(),
        )?;
      }
    }

    Ok(())
  }

  /// Add the edges from a list of connected vertices.
  /// This is useful for building graphs from trees.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let mut graph = WeightedGraph::<10>::new();
  ///
  /// graph.from_vecs(&vec![
  ///   (vec![0, 1, 2], vec![1.0, 2.0]),
  ///   (vec![1, 3, 4], vec![0.1, 3.0])
  /// ]);
  ///
  /// assert!(graph.has_edge(0, 1));
  /// assert!(graph.has_edge(1, 2));
  /// assert!(graph.has_edge(1, 3));
  /// assert!(graph.has_edge(3, 4));
  /// // This should not happen.
  /// assert!(!graph.has_edge(1, 0));
  /// ```
  pub fn from_vecs(
    &mut self,
    vecs: &Vec<(Vec<usize>, Vec<f32>)>,
  ) {
    for (edges, weights) in vecs {
      let mut iter = edges.windows(2).zip(weights);
      while let Some((&[a, b], &weigth)) = iter.next() {
        self.add_edge(a, b, weigth);
      }
    }
  }

  /// Create a graph of `size` with no edges.
  /// ```
  /// use graphs::WeightedGraph;
  ///
  /// let graph = WeightedGraph::<10_000>::new();
  /// ```
  pub const fn new() -> WeightedGraph<N> {
    const EMPTY_VEC: Vec<(usize, f32)> = vec![];
    WeightedGraph {
      size: N,
      data: [EMPTY_VEC; N],
    }
  }
}

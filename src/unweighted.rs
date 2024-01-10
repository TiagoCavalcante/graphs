//! Graph struct and implementation.

use super::rand::{BoolRng, UniformRng};

use std::fs::File;
use std::io::{BufRead, BufReader, Write};

/// A unweighted graph represented using an
/// [adjacency list](https://en.wikipedia.org/wiki/Adjacency_list).
/// ```
/// use graphs::Graph;
///
/// // I told you, fast and easy.
/// let size = 1_000_000;
/// let graph = Graph::new(size);
/// // The overhead is very small (note that this is not the
/// // size of the data).
/// assert!(std::mem::size_of_val(&graph) == 32);
/// ```
pub struct Graph {
  /// The number of vertices in the graph.
  /// ```
  /// use graphs::Graph;
  ///
  /// let size = 10_000;
  /// let graph = Graph::new(size);
  /// assert_eq!(graph.size, size);
  /// ```
  pub size: usize,
  /// The adjacency list, you should not use this directly,
  /// if you want to get the neighbors of a vertex use
  /// [Graph::get_neighbors] instead.
  data: Vec<Vec<usize>>,
}

impl Graph {
  /// Add an edge between the vertices `a` and `b`.
  ///
  /// This is undefined behavior if already there is an
  /// edge between `a` and `b`, so if you are not sure if
  /// this edge already exists you should use
  /// [Graph::has_edge].
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  ///
  /// graph.fill(0.8);
  ///
  /// // We want to ensure that there is an edge between the
  /// // vertex 0 and the vertex 1.
  /// if !graph.has_edge(0, 1) {
  ///   graph.add_edge(0, 1);
  /// }
  /// ```
  ///
  /// This is undefined behavior in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [Graph::add_edge_undirected] instead.
  pub fn add_edge(&mut self, a: usize, b: usize) {
    self.data[a].push(b);
  }

  /// Add an edge between the vertices `a` and `b`.
  ///
  /// This is undefined behavior if already there is an
  /// edge between `a` and `b`, so if you are not sure if
  /// this edge already exists you should use
  /// [Graph::has_edge].
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  ///
  /// graph.fill_undirected(0.8);
  ///
  /// // We want to ensure that there is an edge between the
  /// // vertex 0 and the vertex 1.
  /// if !graph.has_edge(0, 1) {
  ///   graph.add_edge_undirected(0, 1);
  /// }
  /// ```
  ///
  /// This is undefined behavior in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [Graph::add_edge] instead.
  pub fn add_edge_undirected(
    &mut self,
    a: usize,
    b: usize,
  ) {
    self.data[a].push(b);
    self.data[b].push(a);
  }

  /// Remove the edge from `a` to `b` in a directed graph.
  /// This is undefined behavior if there isn't an edge
  /// between `a` and `b`, so if you are not sure if this
  /// edge exists you should use [Graph::has_edge].
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  /// graph.fill(0.7);
  ///
  /// // We don't want an edge between 0 and 9, we are not
  /// // sure it it exists, so we check it it exists, and
  /// // if it does, we remove it.
  /// if graph.has_edge(0, 9) {
  ///   graph.remove_edge(0, 9);
  /// }
  /// ```
  ///
  /// This is undefined behavior in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [Graph::remove_edge_undirected]
  /// instead.
  pub fn remove_edge(&mut self, a: usize, b: usize) {
    let b_position =
      self.data[a].iter().position(|&v| v == b).unwrap();
    // Remove b from a.
    self.data[a].swap_remove(b_position);
  }

  /// Remove the edge between the vertices `a` and `b` in an
  /// undirected graph.
  ///
  /// This is undefined behavior if there isn't an edge
  /// between `a` and `b`, so if you are not sure if this
  /// edge exists you should use [Graph::has_edge].
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  /// graph.fill_undirected(0.5);
  ///
  /// // We want to ensure there is no edge between the
  /// // vertex 0 and the vertex 9.
  /// if graph.has_edge(0, 9) {
  ///   graph.remove_edge_undirected(0, 9);
  /// }
  /// ```
  ///
  /// This is undefined behavior in a
  /// [directed graph](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [Graph::remove_edge] instead.
  pub fn remove_edge_undirected(
    &mut self,
    a: usize,
    b: usize,
  ) {
    let b_position =
      self.data[a].iter().position(|&v| v == b).unwrap();
    // Remove b from a.
    self.data[a].swap_remove(b_position);

    // Remove a from b.
    let a_position =
      self.data[b].iter().position(|&v| v == a).unwrap();
    self.data[b].swap_remove(a_position);
  }

  /// Returns whether there is an edge between the vertices
  /// `a` and `b`.
  ///
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  /// graph.fill(0.1);
  ///
  /// if graph.has_edge(0, 1) {
  ///   println!("We are lucky!");
  /// }
  /// ```
  ///
  /// This is slow and should be replaced with a loop over
  /// the neighbors everywhere it is possible.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  /// graph.fill(0.5);
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
  /// for neighbor in graph.get_neighbors(vertex) {
  ///   println!("{vertex} -> {neighbor}");
  /// }
  /// ```
  pub fn has_edge(&self, a: usize, b: usize) -> bool {
    self.data[a].iter().any(|&neighbor| neighbor == b)
  }

  /// Add edges between `vertex` and each neighbor of
  /// `neighbors`, it is usually used in conjunction with
  /// `pop_edges`.
  /// ```
  /// use graphs::Graph;
  ///
  /// fn shortest_path(
  ///  graph: &Graph,
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
  ///    for &vertex in graph.get_neighbors(current) {
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
  /// let mut graph = Graph::new(10);
  /// graph.fill(0.3);
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
  ///
  /// This is undefined behavior in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [Graph::add_edges_undirected] instead.
  pub fn add_edges(
    &mut self,
    vertex: usize,
    neighbors: &Vec<usize>,
  ) {
    for &neighbor in neighbors {
      self.add_edge(vertex, neighbor);
    }
  }

  /// Add edges between `vertex` and each neighbor of
  /// `neighbors`, it is usually used in conjunction with
  /// `pop_edges_undirected`.
  /// ```
  /// use graphs::Graph;
  ///
  /// fn shortest_path(
  ///   graph: &Graph,
  ///   start: usize,
  ///   end: usize,
  /// ) -> Option<Vec<usize>> {
  ///   let mut queue = std::collections::VecDeque::new();
  ///
  ///   let mut distance = vec![usize::MAX; graph.size];
  ///   let mut predecessor = vec![usize::MAX; graph.size];
  ///
  ///   distance[start] = 0;
  ///
  ///   queue.push_back(start);
  ///
  ///   while let Some(current) = queue.pop_front() {
  ///     for &vertex in graph.get_neighbors(current) {
  ///       if distance[vertex] == usize::MAX {
  ///         distance[vertex] = distance[current] + 1;
  ///         predecessor[vertex] = current;
  ///         queue.push_back(vertex);
  ///
  ///         if vertex == end {
  ///           let mut path = vec![end];
  ///           let mut current = end;
  ///           while predecessor[current] != usize::MAX {
  ///             current = predecessor[current];
  ///             path.push(current);
  ///           }
  ///
  ///           path.reverse();
  ///
  ///           return Some(path);
  ///         }
  ///       }
  ///     }
  ///   }
  ///
  ///   return None;
  /// }
  ///
  /// let mut graph = Graph::new(10);
  /// graph.fill_undirected(0.5);
  ///
  /// let vertex = 5;
  /// let start = 0;
  /// let end = 9;
  ///
  /// let neighbors = graph.pop_edges_undirected(vertex);
  /// let path_without_vertex =
  ///    shortest_path(&graph, start, end);
  /// // Restore the edges.
  /// graph.add_edges_undirected(vertex, &neighbors);
  /// ```
  ///
  /// This is undefined behavior in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [Graph::add_edges] instead.
  pub fn add_edges_undirected(
    &mut self,
    vertex: usize,
    neighbors: &Vec<usize>,
  ) {
    for &neighbor in neighbors {
      self.add_edge_undirected(vertex, neighbor);
    }
  }

  /// Returns the neighbors of `vertex` and remove the edges
  /// between `vertex` and its neighbors.
  /// This may be useful in algorithms like
  /// [k-th shortest path](https://en.wikipedia.org/wiki/Yen's_algorithm).
  ///
  /// This is undefined behavior in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [Graph::pop_edges_undirected] instead.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(50);
  /// graph.fill(1.0);
  ///
  /// // Pop the edges of all even vertices.
  /// for vertex in (0..50).step_by(2) {
  ///   graph.pop_edges(vertex);
  /// }
  /// ```
  pub fn pop_edges(&mut self, vertex: usize) -> Vec<usize> {
    let neighbors = self.data[vertex].clone();

    self.data[vertex].clear();

    neighbors
  }

  /// Returns the neighbors of `vertex` and remove the edges
  /// between `vertex` and its neighbors.
  /// This may be useful in algorithms like
  /// [k-th shortest path](https://en.wikipedia.org/wiki/Yen's_algorithm).
  ///
  /// This is undefined behavior in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [Graph::pop_edges] instead.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(100);
  /// graph.fill_undirected(1.0);
  ///
  /// // Pop the edges of all even vertices.
  /// for vertex in (0..100).step_by(2) {
  ///   graph.pop_edges_undirected(vertex);
  /// }
  /// ```
  pub fn pop_edges_undirected(
    &mut self,
    vertex: usize,
  ) -> Vec<usize> {
    let neighbors = self.data[vertex].clone();
    for &neighbor in &neighbors {
      let position = self.data[neighbor]
        .iter()
        .position(|&v| v == vertex)
        .unwrap();

      self.data[neighbor].swap_remove(position);
    }

    self.data[vertex].clear();

    neighbors
  }

  /// Returns the neighbors of a vertex.
  /// As the graph is represented using an
  /// [adjacency list](https://en.wikipedia.org/wiki/Adjacency_list)
  /// this is an instantaneous operation, and is going to be
  /// inlined.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(1_000);
  /// graph.fill_until(0.1);
  ///
  /// // This whole loop is going to be striped out when
  /// // compiling with --release.
  /// for vertex in 0..graph.size {
  ///   graph.get_neighbors(vertex);
  /// }
  /// ```
  #[inline]
  pub fn get_neighbors(
    &self,
    vertex: usize,
  ) -> &Vec<usize> {
    &self.data[vertex]
  }

  /// Returns the maximum "density" of the graph, that is,
  /// the maximum number of real edges over the maximum
  /// number of real edges plus the number of edges from a
  /// vertex to itself.
  ///
  /// If you want to calculate the density of the graph use
  /// [Graph::density] instead.
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
  /// If you didn't understand what this function does,
  /// don't worry, you aren't really supposed to use this.
  ///
  /// ```
  /// use graphs::Graph;
  ///
  /// let size = 100;
  ///
  /// let mut graph = Graph::new(size);
  /// graph.fill(1.0);
  ///
  /// assert!(graph.max_data_density() < graph.density());
  /// ```
  pub fn max_data_density(&self) -> f32 {
    (self.size - 1) as f32 / self.size as f32
  }

  /// Returns the maximum number of edges in a
  /// [directed graph](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [Graph::max_number_of_edges_undirected]
  /// instead.
  ///
  /// Note that the maximum number of edges in a
  /// [directed graph](https://en.wikipedia.org/wiki/Directed_graph)
  /// is always the double of the number of edges in the
  /// equivalent
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph).
  /// ```
  /// use graphs::Graph;
  ///
  /// let graph = Graph::new(3);
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

  /// Returns the maximum number of edges in a
  /// [undirected graph](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [Graph::max_number_of_edges] instead.
  ///
  /// Note that the maximum number of edges in a
  /// [undirected graph](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// is always half of the number of edges in the equivalent
  /// [directed graph](https://en.wikipedia.org/wiki/Directed_graph).
  /// ```
  /// use graphs::Graph;
  ///
  /// let graph = Graph::new(3);
  /// // The possible edges are:
  /// // 0 <-> 1
  /// // 0 <-> 2
  /// // 1 <-> 2
  /// assert_eq!(graph.max_number_of_edges_undirected(), 3);
  /// ```
  pub const fn max_number_of_edges_undirected(
    &self,
  ) -> usize {
    self.max_number_of_edges() / 2
  }

  /// Returns the density of a graph, that is, the ratio
  /// between the number of edges and the maximum number of
  /// possible edges.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(1_000);
  /// graph.fill_until(0.1);
  ///
  /// let density = graph.density();
  /// assert!(0.09 < density && density < 0.11);
  ///
  /// graph.clear();
  ///
  /// graph.fill_undirected(0.1);
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

  /// Randomly add edges to the graph until it reaches the
  /// desired density.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  /// graph.fill(1.0);
  ///
  /// assert!(graph.has_edge(0, 9));
  /// ```
  ///
  /// If you want to do this in a graph that already have
  /// edges you need to use
  /// [Graph::fill_until] instead.
  ///
  /// [Graph::fill_until] is faster for sparse graphs.
  ///
  /// This is undefined behavior in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [Graph::fill_undirected] instead.
  pub fn fill(&mut self, density: f32) {
    let real_density = density / self.max_data_density();

    let mut edge_rng = BoolRng::new(real_density);

    for i in 0..self.size {
      for j in 0..self.size {
        // This ensures we don't add edges between an vertex
        // and itself.
        if i != j && edge_rng.sample() {
          self.add_edge(i, j);
        }
      }
    }
  }

  /// Randomly add edges to the graph until it reaches the
  /// desired density.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  /// graph.fill_undirected(1.0);
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
  /// This is undefined behavior in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [Graph::fill] instead.
  pub fn fill_undirected(&mut self, density: f32) {
    let real_density = density / self.max_data_density();

    let mut edge_rng = BoolRng::new(real_density);

    for i in 0..self.size {
      for j in 0..self.size {
        // This ensures we don't add edges between an vertex
        // and itself, or that we add an edge twice.
        if i < j && edge_rng.sample() {
          self.add_edge_undirected(i, j);
        }
      }
    }
  }

  /// Randomly add edges to the graph until it reaches the
  /// desired density.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  ///
  /// graph.add_edge(0, 1);
  /// graph.add_edge(1, 2);
  /// graph.add_edge(2, 3);
  ///
  /// assert!(!graph.has_edge(0, 9));
  ///
  /// unsafe {
  ///   graph.fill_until(0.3);
  /// }
  ///
  /// let density = graph.density();
  ///
  /// assert!(0.2 < density && density < 0.4);
  /// ```
  ///
  /// [Graph::fill] is faster for dense graphs, but only
  /// works with empty graphs.
  ///
  /// This is undefined behavior in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [Graph::fill_until_undirected]
  /// instead.
  ///
  /// # Safety
  /// Expect this to run forever for any density above 0.7.
  pub fn fill_until(&mut self, density: f32) {
    let real_density = density - self.density();

    let mut remaining_edges = (real_density
      // This is squared because we need to "throw the coin"
      // for each pair of vertices.
      * self.size.pow(2) as f32)
      as usize;

    let mut vertex_rng = UniformRng::new(0, self.size);

    while remaining_edges != 0 {
      let a = vertex_rng.sample();
      let b = vertex_rng.sample();

      if a != b && !self.has_edge(a, b) {
        self.add_edge(a, b);

        remaining_edges -= 1;
      }
    }
  }

  /// Randomly add edges to the graph until it reaches the
  /// desired density.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  ///
  /// graph.add_edge_undirected(0, 1);
  /// graph.add_edge_undirected(1, 2);
  /// graph.add_edge_undirected(2, 3);
  ///
  /// assert!(!graph.has_edge(0, 9));
  ///
  /// unsafe {
  ///   graph.fill_until_undirected(0.3);
  /// }
  ///
  /// let density = graph.density();
  ///
  /// assert!(0.2 < density && density < 0.4);
  /// ```
  ///
  /// [Graph::fill_undirected] is faster for dense graphs,
  /// but only works in empty graphs.
  ///
  /// This is undefined behavior in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [Graph::fill_until] instead.
  ///
  /// # Safety
  /// Expect this to run forever for any density above 0.7.
  pub unsafe fn fill_until_undirected(
    &mut self,
    density: f32,
  ) {
    let real_density = density - self.density();

    let mut remaining_edges = (real_density
      // This is squared because we need to "throw the coin"
      // for each pair of vertices.
      * self.size.pow(2) as f32
      // And divided by 2 because when we add a connection
      // we add 2 edges, as the graph is undirected.
      * 0.5) as usize;

    let mut vertex_rng = UniformRng::new(0, self.size);

    while remaining_edges != 0 {
      let a = vertex_rng.sample();
      let b = vertex_rng.sample();

      if a != b && !self.has_edge(a, b) {
        self.add_edge_undirected(a, b);

        remaining_edges -= 1;
      }
    }
  }

  /// Remove all edges from the graph.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  /// graph.fill(1.0);
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
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(100);
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
      let edge = line?
        .split_whitespace()
        .filter_map(|s| s.parse().ok())
        .collect::<Vec<_>>();

      self.add_edge(edge[0], edge[1]);
    }

    Ok(())
  }

  /// Save the graph to `path`.
  /// ```no_run
  /// use graphs::Graph;
  ///
  /// let mut graph1 = Graph::new(100);
  ///
  /// graph1.fill(0.3);
  ///
  /// graph1.save("./graphs.grs");
  ///
  /// let mut graph2 = Graph::new(100);
  ///
  /// match graph2.load("./graph.grs") {
  ///   Ok(_) => println!("Success!"),
  ///   Err(_) => panic!("An error occurred"),
  /// }
  /// ```
  pub fn save(&self, path: &str) -> std::io::Result<()> {
    let mut file = File::create(path)?;

    for vertex in 0..self.size {
      for &neighbor in self.get_neighbors(vertex) {
        file.write_all(
          format!("{} {}\n", vertex, neighbor).as_bytes(),
        )?;
      }
    }

    Ok(())
  }

  /// Add the edges from a list of connected vertices.
  /// This is useful for building graphs from trees.
  /// ```
  /// use graphs::Graph;
  ///
  /// let mut graph = Graph::new(10);
  ///
  /// graph.from_vecs(&vec![vec![0, 1, 2], vec![1, 3, 4]]);
  ///
  /// assert!(graph.has_edge(0, 1));
  /// assert!(graph.has_edge(1, 2));
  /// assert!(graph.has_edge(1, 3));
  /// assert!(graph.has_edge(3, 4));
  /// // This should not happen.
  /// assert!(!graph.has_edge(1, 0));
  /// ```
  pub fn from_vecs(&mut self, vecs: &Vec<Vec<usize>>) {
    for vec in vecs {
      let mut iter = vec.windows(2);
      while let Some(&[a, b]) = iter.next() {
        self.add_edge(a, b);
      }
    }
  }

  /// Create a graph of `size` with no edges.
  /// ```
  /// use graphs::Graph;
  ///
  /// let size = 10_000;
  /// let graph = Graph::new(size);
  /// ```
  pub fn new(size: usize) -> Graph {
    Graph {
      size,
      data: vec![vec![]; size],
    }
  }
}

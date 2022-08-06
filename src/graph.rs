use super::rand::UniformRng;

/// A unweighted graph represented using an
/// [adjacency list](https://en.wikipedia.org/wiki/Adjacency_list).
pub struct Graph {
  /// The number of vertices in the graph.
  pub size: usize,
  data: Vec<Vec<usize>>,
}

impl Graph {
  /// Add an edge between the vertices `a` and `b`.
  ///
  /// This is undefined behaviour if already there is an
  /// edge between `a` and `b`, so if you are not sure if
  /// this edge already exists you should use
  /// [`Graph::has_edge`].
  /// ```
  /// if !graph.has_edge(a, b) {
  ///   graph.add_edge(a, b);
  /// }
  /// ```
  ///
  /// This is undefined behaviour in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [`Graph::add_edge_undirected`] instead.
  pub fn add_edge(&mut self, a: usize, b: usize) {
    self.data[a].push(b);
  }

  /// Add an edge between the vertices `a` and `b`.
  ///
  /// This is undefined behaviour if already there is an
  /// edge between `a` and `b`, so if you are not sure if
  /// this edge already exists you should use
  /// [`Graph::has_edge`].
  /// ```
  /// if !graph.has_edge(a, b) {
  ///   graph.add_edge(a, b);
  /// }
  /// ```
  ///
  /// This is undefined behaviour in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [`Graph::add_edge`] instead.
  pub fn add_edge_undirected(
    &mut self,
    a: usize,
    b: usize,
  ) {
    self.data[a].push(b);
    self.data[b].push(a);
  }

  /// Remove the edge from `a` to `b` in a directed graph.
  /// This is undefined behaviour if there isn't an edge
  /// between `a` and `b`, so if you are not sure if this
  /// edge exists you should use [`Graph::has_edge`].
  /// ```
  /// if graph.has_edge(a, b) {
  ///   graph.remove_edge(a, b);
  /// }
  /// ```
  ///
  /// This is undefined behaviour in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [`Graph::remove_edge_undirected`]
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
  /// This is undefined behaviour if there isn't an edge
  /// between `a` and `b`, so if you are not sure if this
  /// edge exists you should use [`Graph::has_edge`].
  /// ```
  /// if graph.has_edge(a, b) {
  ///   graph.remove_edge(a, b);
  /// }
  /// ```
  ///
  /// This is undefined behaviour in a
  /// [directed graph](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [`Graph::remove_edge`] instead.
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
  pub fn has_edge(&self, a: usize, b: usize) -> bool {
    self.data[a].iter().any(|&neighbor| neighbor == b)
  }

  /// Add edges between `vertex` and each neighbor of
  /// `neighbors`, it is usually used in conjunction with
  /// `pop_edges`.
  /// ```
  /// let neighbors = graph.pop_edges(vertex);
  /// let path_without_vertex =
  ///   path::shortest_path(&graph, a, b);
  /// // Restore the edges.
  /// graph.add_edges(vertex, neighbors);
  /// ```
  ///
  /// This is undefined behaviour in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [`Graph::add_edges_undirected`] instead.
  pub fn add_edges(
    &mut self,
    vertex: usize,
    neighbors: &Vec<usize>,
  ) {
    for neighbor in neighbors {
      self.add_edge(vertex, *neighbor);
    }
  }

  /// Add edges between `vertex` and each neighbor of
  /// `neighbors`, it is usually used in conjunction with
  /// `pop_edges_undirected`.
  /// ```
  /// let neighbors = graph.pop_edges_undirected(vertex);
  /// let path_without_vertex =
  ///   path::shortest_path(&graph, a, b);
  /// // Restore the edges.
  /// graph.add_edges_undirected(vertex, neighbors);
  /// ```
  ///
  /// This is undefined behaviour in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [`Graph::add_edges`] instead.
  pub fn add_edges_undirected(
    &mut self,
    vertex: usize,
    neighbors: &Vec<usize>,
  ) {
    for neighbor in neighbors {
      self.add_edge_undirected(vertex, *neighbor);
    }
  }

  /// Returns the neighbors of `vertex` and remove the edges
  /// between `vertex` and its neighbors.
  /// This may be useful in alorithms like
  /// [k-th shortest path](https://en.wikipedia.org/wiki/Yen's_algorithm).
  ///
  /// This is undefined behaviour in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [`Graph::pop_edges_undirected`] instead.
  pub fn pop_edges(&mut self, vertex: usize) -> Vec<usize> {
    let neighbors = self.data[vertex].clone();

    self.data[vertex].clear();

    neighbors
  }

  /// Returns the neighbors of `vertex` and remove the edges
  /// between `vertex` and its neighbors.
  /// This may be useful in alorithms like
  /// [k-th shortest path](https://en.wikipedia.org/wiki/Yen's_algorithm).
  ///
  /// This is undefined behaviour in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [`Graph::pop_edges`] instead.
  pub fn pop_edges_undirected(
    &mut self,
    vertex: usize,
  ) -> Vec<usize> {
    let neighbors = self.data[vertex].clone();
    for neighbor in &neighbors {
      let position = self.data[*neighbor]
        .iter()
        .position(|v| *v == vertex)
        .unwrap();

      self.data[*neighbor].swap_remove(position);
    }

    self.data[vertex].clear();

    neighbors
  }

  /// Returns the neighbors of a vertex.
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
  /// For example:
  /// The
  /// [matrix representation](https://en.wikipedia.org/wiki/Adjacency_matrix)
  /// of a [complete graph](https://en.wikipedia.org/wiki/Complete_graph)
  /// with 3 vertices is the following:
  /// $$\LARGE{
  ///   \begin{bmatrix}
  ///   0 & 1 & 1 \\
  ///   1 & 0 & 1 \\
  ///   1 & 1 & 0
  ///   \end{bmatrix}
  /// }$$
  /// The ones represent that there is an edge between the
  /// vertex with the number of the column and the vertex
  /// with the number of the row.
  /// The zeros represent that there isn't an edge, in this
  /// case, between a vertex and itself.
  /// This function returns the number of ones over the size
  /// of the matrix representation.
  /// This is only meaningful for small graphs as the
  /// maximum "density" converges to one in big graphs.
  pub fn max_data_density(&self) -> f32 {
    (self.size as f32 - 1.0) / self.size as f32
  }

  /// Returns the maximum number of edges in the graph.
  pub fn maximum_number_of_edges(&self) -> usize {
    self.size * (self.size - 1)
  }

  /// Returns the density of the graph, that is, the ratio
  /// between the number of edges and the maximum number of
  /// possible edges.
  pub fn density(&self) -> f32 {
    let mut edges = 0;

    for neighbors in &self.data {
      edges += neighbors.len();
    }

    edges as f32 / self.maximum_number_of_edges() as f32
  }

  /// Randomly add edges to the graph until it reaches the
  /// desired density.
  /// If you want to do this in a graph that already have
  /// edges you need to use
  /// [`Graph::fill_until`] instead.
  ///
  /// This is undefined behaviour in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [`Graph::fill_undirected`] instead.
  pub fn fill(&mut self, density: f32) {
    let real_density = density / self.max_data_density();

    let edges = (real_density
      // This is squared because we need to "throw the coin"
      // for each pair of vertices.
      * self.size.pow(2) as f32) as usize;

    let mut vertex_rng = UniformRng::new(0, self.size);

    for _ in 0..edges {
      let a = vertex_rng.sample();
      let b = vertex_rng.sample();

      if a != b {
        self.add_edge(a, b);
      }
    }
  }

  /// Randomly add edges to the graph until it reaches the
  /// desired density.
  /// If you want to do this in a graph that already have
  /// edges you need to use
  /// [`Graph::fill_until_undirected`] instead.
  ///
  /// This is undefined behaviour in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [`Graph::fill`] instead.
  pub fn fill_undirected(&mut self, density: f32) {
    let real_density = density / self.max_data_density();

    let edges = (real_density
      // This is squared because we need to "throw the coin"
      // for each pair of vertices.
      * self.size.pow(2) as f32
      // And divided by 2 because when we add a connection
      // we add 2 edges, as the graph is undirected.
      * 0.5) as usize;

    let mut vertex_rng = UniformRng::new(0, self.size);

    for _ in 0..edges {
      let a = vertex_rng.sample();
      let b = vertex_rng.sample();

      if a != b {
        self.add_edge_undirected(a, b);
      }
    }
  }

  /// Randomly add edges to the graph until it reaches the
  /// desired density.
  ///
  /// [`Graph::fill`] is faster, but only works in graphs
  /// with no edges.
  ///
  /// This is undefined behaviour in
  /// [undirected graphs](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph),
  /// if your graph is
  /// [undirected](https://en.wikipedia.org/wiki/Graph_(discrete_mathematics)#Graph)
  /// you should use [`Graph::fill_until_undirected`]
  /// instead.
  pub fn fill_until(&mut self, density: f32) {
    let real_density =
      density / self.max_data_density() - self.density();

    let mut remaining_edges = (real_density
      // This is squared because we need to "throw the coin"
      // for each pair of vertices.
      * self.size.pow(2) as f32)
      as usize;

    let mut vertex_rng = UniformRng::new(0, self.size);

    loop {
      let a = vertex_rng.sample();
      let b = vertex_rng.sample();

      if a != b && !self.has_edge(a, b) {
        self.add_edge(a, b);

        remaining_edges -= 1;

        if remaining_edges == 0 {
          break;
        }
      }
    }
  }

  /// Randomly add edges to the graph until it reaches the
  /// desired density.
  ///
  /// [`Graph::fill_undirected`] is faster, but only works
  /// in graphs with no edges.
  ///
  /// This is undefined behaviour in
  /// [directed graphs](https://en.wikipedia.org/wiki/Directed_graph),
  /// if your graph is
  /// [directed](https://en.wikipedia.org/wiki/Directed_graph)
  /// you should use [`Graph::fill_until`] instead.
  pub fn fill_until_undirected(&mut self, density: f32) {
    let real_density =
      density / self.max_data_density() - self.density();

    let edges = (real_density
      // This is squared because we need to "throw the coin"
      // for each pair of vertices.
      * self.size.pow(2) as f32
      // And divided by 2 because when we add a connection
      // we add 2 edges, as the graph is undirected.
      * 0.5) as usize;

    let mut vertex_rng = UniformRng::new(0, self.size);

    for _ in 0..edges {
      let a = vertex_rng.sample();
      let b = vertex_rng.sample();

      if a != b {
        self.add_edge_undirected(a, b);
      }
    }
  }

  /// Remove all edges from the graph.
  pub fn clear(&mut self) {
    for neighbors in &mut self.data {
      neighbors.clear();
    }
  }

  /// Create a graph of `size` with no edges.
  /// ```
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

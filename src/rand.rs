//! Wrappers over the rand crate.

use rand::distributions::{Distribution, Uniform};
use rand::rngs::StdRng;
use rand::SeedableRng;
use rand_distr::Normal;

/// Uniform random number generator.
/// ```compile_fail
/// // This is a private field and should not be accessible
/// // to the end user.
/// let mut uniform_rng = Uniform::new(1, 6);
/// let dice: usize = uniform_rng.sample();
/// assert!(1 <= dice && dice <= 6);
/// ```
pub struct UniformRng {
  uniform_rng: Uniform<usize>,
  rng: StdRng,
}

impl UniformRng {
  /// Creates a new `UniformRng` with a specified range.
  /// ```compile_fail
  /// let mut rng = UniformRng::new(1, 10);
  /// let random_number = rng.sample();
  /// assert!(1 <= random_number && random_number < 10);
  /// ```
  pub fn new(start: usize, end: usize) -> UniformRng {
    let uniform_rng = Uniform::from(start..end);
    let rng = StdRng::from_entropy();

    UniformRng { uniform_rng, rng }
  }

  /// Creates a new `UniformRng` with a specified range and
  /// a seed for reproducible results.
  /// ```compile_fail
  /// let seed = 12345;
  /// let mut rng = UniformRng::from_seed(1, 10, seed);
  /// let random_number = rng.sample();
  /// ```
  pub fn from_seed(
    start: usize,
    end: usize,
    seed: u64,
  ) -> UniformRng {
    let uniform_rng = Uniform::from(start..end);
    let rng = StdRng::seed_from_u64(seed);

    UniformRng { uniform_rng, rng }
  }

  /// Samples a random number within the specified range.
  /// ```compile_fail
  /// let mut rng = UniformRng::new(1, 100);
  /// let random_number = rng.sample();
  /// assert!(1 <= random_number && random_number < 100);
  /// ```
  pub fn sample(&mut self) -> usize {
    self.uniform_rng.sample(&mut self.rng)
  }
}

/// Uniform random positive number generator.
/// ```compile_fail
/// // This is a private field and should not be accessible
/// // to the end user.
/// let mut normal_rng = Normal::new(1.0, 0.1);
/// assert!(normal_rng.sample() > 0);
/// ```
pub struct NormalRng {
  normal_rng: Normal<f32>,
  rng: StdRng,
}

impl NormalRng {
  /// Creates a new `NormalRng` with the specified mean and
  /// standard deviation.
  /// ```compile_fail
  /// let mut rng = NormalRng::new(5.0, 2.0);
  /// let random_number = rng.sample();
  /// ```
  pub fn new(mean: f32, std_dev: f32) -> NormalRng {
    let normal_rng = Normal::new(mean, std_dev).unwrap();
    let rng = StdRng::from_entropy();

    NormalRng { normal_rng, rng }
  }

  /// Creates a new `NormalRng` with the specified mean,
  /// standard deviation, and seed for reproducible results.
  /// ```compile_fail
  /// let seed = 12345;
  /// let mut rng = NormalRng::from_seed(5.0, 2.0, seed);
  /// let random_number = rng.sample();
  /// ```
  pub fn from_seed(
    mean: f32,
    std_dev: f32,
    seed: u64,
  ) -> NormalRng {
    let normal_rng = Normal::new(mean, std_dev).unwrap();
    let rng = StdRng::seed_from_u64(seed);

    NormalRng { normal_rng, rng }
  }

  /// Samples a random number according to the normal
  /// distribution.
  /// ```compile_fail
  /// let mut rng = NormalRng::new(0.0, 1.0);
  /// let random_number = rng.sample();
  /// ```
  pub fn sample(&mut self) -> f32 {
    self.normal_rng.sample(&mut self.rng).abs()
  }
}

/// Random boolean generator.
/// ```compile_fail
/// // This is a private field and should not be accessible
/// // to the end user.
/// let mut bool_rng = BoolRng::new(0.5);
/// let is_true: bool = bool_rng.sample();
/// ```
pub struct BoolRng {
  uniform_rng: Uniform<usize>,
  rng: StdRng,
  threshold: usize,
}

impl BoolRng {
  /// Creates a new instance of `BoolRng` with a given
  /// probability of yielding `true`.
  /// ```compile_fail
  /// let mut rng = BoolRng::new(0.5);
  /// let result: bool = rng.sample();
  /// // There is a 50% chance that `result` is true.
  /// ```
  pub fn new(probability: f32) -> BoolRng {
    let uniform_rng = Uniform::from(0..usize::MAX);
    let rng = StdRng::from_entropy();

    BoolRng {
      uniform_rng,
      threshold: (probability * usize::MAX as f32) as usize,
      rng,
    }
  }

  /// Creates a new `BoolRng` with a specific seed and
  /// probability.
  /// This method allows for consistent and reproducible
  /// random boolean generation.
  /// ```compile_fail
  /// let seed = 12345;
  /// let mut rng = BoolRng::from_seed(0.5, seed);
  /// let result = rng.sample();
  /// ```
  pub fn from_seed(probability: f32, seed: u64) -> BoolRng {
    let uniform_rng = Uniform::from(0..usize::MAX);
    let rng = StdRng::seed_from_u64(seed);

    BoolRng {
      uniform_rng,
      threshold: (probability * usize::MAX as f32) as usize,
      rng,
    }
  }

  /// Samples a boolean value based on the probability
  /// defined in `BoolRng`.
  /// Returns `true` with the defined probability, and
  /// `false` otherwise.
  /// ```compile_fail
  /// let mut rng = BoolRng::new(0.3);
  /// let result = rng.sample();
  /// // There's a 30% chance that `result` is true
  /// ```
  pub fn sample(&mut self) -> bool {
    self.uniform_rng.sample(&mut self.rng) < self.threshold
  }
}

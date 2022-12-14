//! Wrappers over the rand crate.

use rand::distributions::{Distribution, Uniform};
use rand::rngs::ThreadRng;
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
  rng: ThreadRng,
}

impl UniformRng {
  pub fn new(start: usize, end: usize) -> UniformRng {
    let uniform_rng = Uniform::from(start..end);
    let rng = rand::thread_rng();

    UniformRng { uniform_rng, rng }
  }

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
  rng: ThreadRng,
}

impl NormalRng {
  pub fn new(mean: f32, std_dev: f32) -> NormalRng {
    let normal_rng = Normal::new(mean, std_dev).unwrap();
    let rng = rand::thread_rng();

    NormalRng { normal_rng, rng }
  }

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
  rng: ThreadRng,
  threshold: usize,
}

impl BoolRng {
  /// Receives the probability of yielding `true`.
  pub fn new(probability: f32) -> BoolRng {
    let uniform_rng = Uniform::from(0..usize::MAX);
    let rng = rand::thread_rng();

    BoolRng {
      uniform_rng,
      rng,
      threshold: (probability * usize::MAX as f32) as usize,
    }
  }

  pub fn sample(&mut self) -> bool {
    self.uniform_rng.sample(&mut self.rng) < self.threshold
  }
}

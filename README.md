beware: 100% authentic hallucinations ahead.


# Self-Predictability Gravity: An Informational Framework

This framework presents a mathematically formalized bridge between local information-theoretic optimization and emergent physical mechanics. It operates on a simple premise: **coordinate attraction can emerge from the dynamical requirement of physical states to maintain their own local structural predictability.**

Rather than postulating force fields or metrics *a priori*, this framework derives them by evaluating the bounds of state predictability within wide-sense stationary stochastic systems. By scaling this analysis from discrete lattices to continuous spaces, we show that the minimization of prediction entropy generates emergent dynamics identical to gravity, complete with physical equivalents to Heisenberg uncertainty, quantum decoherence, and general relativity's short-range UV exclusion limits.

---

## Directory and Theorem Map

All core structural claims within this framework are verified under classical Hilbert space foundations in Lean 4. The documentation is organized into the following modules, mapped directly to their formal proofs:

### 1. [Duality and Horizons](duality_horizons.md)
* **Mathematical Focus:** Formulates the unified `ExponentialCovarianceProcess` on arbitrary metric spaces. Specializes this process to 1D discrete lattices ($\mathbb{Z}$) and continuous lines ($\mathbb{R}$) to find exact predictability bounds.
* **Lean 4 Source Files:** `Common.lean`, `Discrete.lean`, `Continuous.lean`
* **Key Proofs:**
  * `unilateral_optimal_mse`: Validates the $C_0(1 - z^{2d})$ error scaling.
  * `bilateral_optimal_mse` & `bilateral_orthogonality`: Proves the projection-based spatial Markov property.
  * `spatial_markov_property_optimality`: Establishes the minimality of boundary predictors.

### 2. [Conjugate Properties and Uncertainty](conjugate.md)
* **Mathematical Focus:** Applies the Wiener–Khinchin theorem to prove that a continuous process cannot be localized in both spatial position and its conjugate spatial frequency (momentum) simultaneously.
* **Lean 4 Source Files:** `Conjugate.lean`
* **Key Proofs:**
  * `entropic_uncertainty_relation`: Proves the exact conjugate scaling relation $\xi \cdot \Delta k = 1$.
  * `process_uncertainty_relation`: Grounds the uncertainty relation within the unified process model.

### 3. [Motion as an Entropic Gradient](motion_entropy.md)
* **Mathematical Focus:** Converts prediction errors into Shannon differential entropy, defining an informational potential energy. Shows that gradient flows minimizing this entropy generate attractive, dissipative forces.
* **Lean 4 Source Files:** `Motion.lean`, `Gravity.lean`
* **Key Proofs:**
  * `continuous_potential_deriv`: Proves that the entropic force $F = -\frac{\gamma}{\xi} \frac{1}{e^{2r/\xi} - 1}$ is the exact negative gradient of the informational potential.
  * `mutual_force_symmetric`: Proves Newton's Third Law for entropic gravity ($F_{12} = -F_{21}$).
  * `mutual_force_monotone`: Verifies asymptotic decay as separation increases.
  * `origin_actor`: Formalizes the "Self-Correcting Actor" trajectory.

### 4. [3D Generalization & Exclusion Boundaries](3d_gravity.md)
* **Mathematical Focus:** Extends the framework to three dimensions. Uses a local UV resolution cutoff to derive a physical exclusion zone.
* **Lean 4 Source Files:** `3d.lean`
* **Key Proofs:**
  * `continuous_3d_exclusion_limit`: Proves the Cauchy-Schwarz Informational Exclusion Boundary $r \ge C_0 / \Lambda$.
  * `continuous_3d_potential_deriv`: Derives the 3D potential derivative and the resulting force field.

### 5. [Diffusion Isomorphisms and Wick Rotation](diffusion_isomorphisms.md)
* **Mathematical Focus:** Maps the dynamics of the framework to quantum mechanical and collective systems.
* **Lean 4 Source Files:** `e_diff_consensus.lean`, `wick_diffusion.lean`
* **Key Proofs:**
  * `decoherence_deriv` & `disagreement_deriv`: Formulates time derivatives of coherence states and multi-agent consensus.
  * `entropic_diffusion_isomorphism`: Establishes the isomorphism between decoherence and consensus under $\mu = 1/(2\tau)$.
  * `wick_rotation_equivalence`: Proves the Wick-rotated equivalence between the Schrödinger equation and damped diffusion.
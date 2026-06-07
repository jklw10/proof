
# Dual Spatial Predictability Horizons

This document presents the mathematical formulations and proofs establishing the spatial limits of state predictability. Using a Hilbert space projection framework, we analyze these horizons across general metric spaces, discrete lattices, and continuous lines.

---

## 1. The Unified Covariance Framework

We represent our physical field as a wide-sense stationary process $u$ mapped to a real Hilbert space $E$ representing the space of random variables. For any metric space $T$ (with distance function $\text{dist}$), the covariance between any two points decays exponentially with distance:

$$\langle u(x), u(y) \rangle = C_0 z^{\text{dist}(x, y)}$$

where $C_0 > 0$ represents the stationary variance, and $z \in (0, 1)$ is the spatial decay factor. This is formalized in Lean 4 as the structure `ExponentialCovarianceProcess`:

```lean
structure ExponentialCovarianceProcess (T : Type*) [MetricSpace T]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  u : T → E
  C0 : ℝ
  z : ℝ
  hC0 : 0 < C0
  hz0 : 0 < z
  hz1 : z < 1
  cov : ∀ x y : T, inner ℝ (u x) (u y) = C0 * z ^ (dist x y)
```

By evaluating the properties of this unified process, we derive the exact performance limits of linear estimators.

---

## 2. The Unilateral Predictability Horizon

The unilateral horizon defines the maximum distance at which a single localized state $u(y)$ can predict another state $u(x)$ to within a specified error tolerance $\delta > 0$.

### Optimal Linear Prediction
For any separation $d = \text{dist}(x, y)$, the optimal least-squares linear predictor of $u(x)$ given $u(y)$ is:
$$\hat{u}(x) = \beta u(y), \quad \text{where } \beta = z^d$$

Under this optimal coefficient, the Mean Squared Error (MSE) is strictly bounded by:
$$\text{MSE}_{\text{uni}}(d) = \|u(x) - \beta u(y)\|^2 = C_0 (1 - z^{2d})$$

This is formally proven in `Common.lean` as:
```lean
theorem unilateral_optimal_mse (P : ExponentialCovarianceProcess T E) (x y : T) (d : ℝ) (hd : dist x y = d) :
    let β_opt := P.z ^ d
    ‖P.u x - β_opt • P.u y‖^2 = P.C0 * (1 - P.z ^ (2 * d))
```

### The Analytical Predictability Limit
Defining the physical spatial correlation length as $\xi = -1 / \ln z$, the condition that the unilateral prediction error remains below a tolerance $\delta < C_0$ restricts the physical distance to a bounded domain $r \le \xi_{\text{abs}}^*$, where:

$$\xi_{\text{abs}}^* = \frac{\xi}{2} \ln \left( \frac{1}{1 - \frac{\delta}{C_0}} \right)$$

This exact equivalence is verified in `Continuous.lean` via:
```lean
theorem continuous_unilateral_horizon_limit (u : ℝ → E) (C0 z δ r : ℝ)
    (h_cov : ∀ x y : ℝ, inner ℝ (u x) (u y) = C0 * z ^ |x - y|)
    (hC0 : 0 < C0) (hz0 : 0 < z) (hz1 : z < 1) (hδ0 : 0 < δ) (hδ : δ < C0) (hr : 0 ≤ r) :
    let P := continuous_to_unified u C0 z h_cov hC0 hz0 hz1
    ‖P.u r - (P.z ^ r) • P.u 0‖^2 ≤ δ ↔ r ≤ xi_abs_star C0 z δ
```

---

## 3. The Bilateral Horizon & Spatial Markov Property

If a state $u(x)$ is positioned along a metric geodesic between boundary observations $u(a)$ and $u(b)$ such that $\text{dist}(a, b) = \text{dist}(a, x) + \text{dist}(x, b)$, the optimal predictor uses both boundary points:

$$\hat{u}(x) = \beta_1 u(a) + \beta_2 u(b)$$

### Spatial Orthogonality (Markov Condition)
The prediction error vector $(u(x) - \hat{u}(x))$ is orthogonal to the subspace spanned by the boundary observations:
$$\langle u(x) - \hat{u}(x), u(a) \rangle = 0 \quad \text{and} \quad \langle u(x) - \hat{u}(x), u(b) \rangle = 0$$

Under this orthogonal projection, the optimal coefficients are:
$$\beta_1 = \frac{z^{d_1} - z^{d_2 + d}}{1 - z^{2d}}, \quad \beta_2 = \frac{z^{d_2} - z^{d_1 + d}}{1 - z^{2d}}$$

where $d_1 = \text{dist}(a, x)$, $d_2 = \text{dist}(x, b)$, and $d = \text{dist}(a, b)$. This results in an optimal bilateral prediction error of:

$$\|u(x) - \hat{u}(x)\|^2 = C_0 \left( \frac{1 - z^{2d_1} - z^{2d_2} + z^{2d}}{1 - z^{2d}} \right)$$

This continuous bilateral projection and its resulting error are formalized in `Continuous.lean` as:
```lean
theorem continuous_bilateral_orthogonality ...
theorem continuous_bilateral_optimal_mse ...
```

---

## 4. Discrete Specialization on the Lattice $\mathbb{Z}$

When specializing to the 1D lattice $\mathbb{Z}$, predicting a node $y$ using its symmetric nearest neighbors $\{x_{-1}, x_1\}$ (where $\text{dist} = 1$) reduces the optimal bilateral prediction error to the local boundary limit:

$$\text{MSE}_{\text{bi}} = C_0 \left( \frac{1 - z^2}{1 + z^2} \right)$$

This is proven in `Discrete.lean` under:
```lean
theorem discrete_bilateral_optimal_mse (u : ℤ → E) (C0 z : ℝ) ...
    ‖y - β_opt • u_comb‖^2 = C0 * ((1 - z^2) / (1 + z^2))
```

### Minimality and the Spatial Markov Property
Because the covariance function decays exponentially, the system forms a first-order spatial autoregressive process, AR(1). This guarantees that the immediate boundary $\{x_{-1}, x_1\}$ acts as a shielding neighborhood.

We verify in Lean 4 that adding wider neighbors (e.g., $x_{-2}$ and $x_2$) to create a 4-node predictor $W$ yields zero further reduction in the minimum prediction error. The bilateral boundary predictor strictly minimizes the MSE:

```lean
theorem spatial_markov_property_optimality {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExponentialCovarianceProcess T E) (x_neg2 x_neg1 y x_1 x_2 : T) ...
    ‖P.u y - Pred‖^2 ≤ ‖P.u y - W‖^2
```
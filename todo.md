# Framework Overview: Self-Predictability Gravity

This framework presents a mathematically rigorous, self-contained bridge between local information-theoretic optimization and emergent physical mechanics. It operates on a simple, universal premise: **physical coordinate attraction (gravity) can emerge from the dynamical requirement of states to maintain their own local structural predictability.**

By analyzing a linear, Gaussian stochastic system, we map the exact boundaries of predictability in discrete and continuous spaces, transitioning from mean squared error (MSE) to Shannon entropy, and finally to physical force fields.

---

## The Three Core Pillars

```
+-------------------------------------------------------------+
| 1. Dual Spatial Predictability Horizons                    |
|    - Defines unilateral and bilateral prediction bounds.   |
|    - Proves the strict lower bound of boundary prediction. |
+-------------------------------------------------------------+
                              |
                              v
+-------------------------------------------------------------+
| 2. Continuous SPDE & Hilbert Space Projections             |
|    - Extends the discrete lattice to a continuous SPDE.     |
|    - Formulates prediction as projections in L² spaces.     |
+-------------------------------------------------------------+
                              |
                              v
+-------------------------------------------------------------+
| 3. Motion as an Entropic Gradient                           |
|    - Converts predictability error (MSE) into entropy.     |
|    - Derives the entropic force: F = -(γ/ξ) / (e^(2r/ξ) - 1)|
|    - Recovers a 1/r gravitational attractor at short ranges.|
+-------------------------------------------------------------+
```

---

## Directory and Documentation Roadmap

1. **[`duality_horizons.md`](duality_horizons.md)**
   * *Contents:* The formal theorem of dual spatial predictability horizons on a 1D lattice, resolved spectral representations, and discrete algebraic derivations.
2. **[`continuous_spde.md`](continuous_spde.md)**
   * *Contents:* The scaling limit of the lattice system to the stochastic heat equation, formulation in $L^2(\mathbb{R})$, and continuous-space projection proofs verified in Lean 4.
3. **[`motion_entropy.md`](motion_entropy.md)**
   * *Contents:* The conceptual derivation of motion as a gradient flow minimizing prediction error. Includes the analytical derivation of the $1/r$ scaling entropic force, connecting it to Active Inference (Friston) and Entropic Gravity (Verlinde).


---

### File 2: `duality_horizons.md`

# Theorem of Dual Spatial Predictability Horizons

This document presents the mathematically rigorous formulation and analytical proofs for the spatial limits of state predictability on an infinite-dimensional discrete lattice under stationary conditions.

---

## Theorem Formulation

Let an infinite-dimensional linear system on the lattice $\mathbb{Z}$ be driven by independent, local white noise. For any given absolute mean squared error (MSE) tolerance $\delta > 0$, the spatial domain within which the state of a node can be predicted under stationary conditions is bounded by two distinct topological horizons:

### 1. The Unilateral Horizon (Single-Probe Limit)
If the state $x_{i+r}$ is predicted using only a single probe $x_i$ at distance $r \ge 1$, the absolute MSE can be bounded by $\delta$ if and only if:
$$\delta \ge \delta_{\min}^{(1)} = C(0) \left(1 - e^{-2/\xi}\right)$$

For any valid tolerance, the predictability domain is the bounded set of integers $1 \le r \le \xi_{\text{abs}}^*$, where the unilateral scale is:
$$\xi_{\text{abs}}^* = \frac{\xi}{2} \ln \left( \frac{1}{1 - \frac{\delta}{C(0)}} \right)$$

### 2. The Bilateral Horizon (Local Boundary Limit)
If the state $x_j$ is predicted collectively using its surrounding neighborhood $\mathcal{N}_d(j) = \{x_k \mid 1 \le |k-j| \le d\}$, the absolute MSE can be bounded by $\delta$ if and only if:
$$\delta \ge \delta_{\min}^{(2)} = C(0) \left( \frac{1 - e^{-2/\xi}}{1 + e^{-2/\xi}} \right)$$

By the spatial Markov property of the stationary state, expanding the predictor beyond the immediate boundary $d=1$ yields zero further reduction in the minimum prediction error.

Here, $C(0)$ is the exact stationary variance of a single node, and $\xi$ is the physical spatial correlation length.

---

## Mathematical Proof

The SDE governing the lattice is:
$$dx_i(t) = -\alpha x_i(t) dt + J \big(x_{i+1}(t) + x_{i-1}(t) - 2x_i(t)\big) dt + \sigma dW_i(t)$$
where $\alpha > 0$ is the dissipation rate, $J > 0$ is the coupling strength, and $\mathbb{E}[dW_i(t) dW_j(t)] = \delta_{ij} dt$.

### Step 1: Spectral Representation (Fourier Divergence Resolution)
To avoid divergence of direct spatial Fourier transforms for non-decaying random sequences, we apply the Spectral Representation Theorem. The stationary process $x_n(t)$ and independent Wiener processes $W_n(t)$ are expressed as stochastic integrals over orthogonal random spectral measures on $k \in [-\pi, \pi]$:
$$x_n(t) = \int_{-\pi}^{\pi} e^{i k n} d\Phi(k, t), \quad W_n(t) = \int_{-\pi}^{\pi} e^{i k n} d\Psi(k, t)$$

where:
$$\mathbb{E}[d(d\Psi(k, t)) d(d\Psi^*(k', t))] = \frac{1}{2\pi} \delta(k - k') dt dk dk'$$

Substituting this into the SDE yields decoupled spectral increments:
$$d\big(d\Phi(k, t)\big) = -\lambda(k) d\Phi(k, t) dt + \sigma d\big(d\Psi(k, t)\big)$$
with dispersion relation $\lambda(k) = \alpha + 4J\sin^2(k/2) > 0$. In the stationary limit ($t \to \infty$), the variance of the spectral increments is:
$$\mathbb{E}[|d\Phi(k, \infty)|^2] = \frac{\sigma^2}{4\pi \left( \alpha + 4J\sin^2(k/2) \right)} dk$$

### Step 2: Integration of the Spatial Covariance
The spatial covariance $C(r)$ for $r = |i - j|$ is:
$$C(r) = \frac{\sigma^2}{4\pi} \int_{-\pi}^{\pi} \frac{\cos(k r)}{\alpha + 2J(1 - \cos k)} dk$$

Evaluating the contour integral yields exact exponential decay:
$$C(r) = C(0) z^r = C(0) e^{-r/\xi}$$
where:
$$C(0) = \frac{\sigma^2}{2\sqrt{\alpha(\alpha + 4J)}}$$
$$e^{-1/\xi} = z = 1 + \frac{\alpha}{2J} - \sqrt{\left(1 + \frac{\alpha}{2J}\right)^2 - 1}$$

### Step 3: Derivation of the Unilateral Horizon
The linear least-squares predictor of $x_{i+r}$ using $x_i$ is $\hat{x}_{i+r} = \beta x_i$. The optimal parameter is the ordinary least squares coefficient $\beta = C(r)/C(0) = e^{-r/\xi}$, yielding:
$$\text{MSE}_{\text{uni}}(r) = C(0)\big(1 - R(r)^2\big) = C(0)\big(1 - e^{-2r/\xi}\big)$$

Imposing the condition $\text{MSE}_{\text{uni}}(r) \le \delta$ (assuming $\delta < C(0)$):
$$e^{-2r/\xi} \ge 1 - \frac{\delta}{C(0)} \implies r \le \xi_{\text{abs}}^* = \frac{\xi}{2} \ln \left( \frac{1}{1 - \frac{\delta}{C(0)}} \right)$$

Requiring that at least one physical neighbor exists within this scale ($\xi_{\text{abs}}^* \ge 1$) yields the minimum required tolerance:
$$\delta \ge \delta_{\min}^{(1)} = C(0) \left(1 - e^{-2/\xi}\right)$$

### Step 4: Derivation of the Bilateral Horizon (Spatial Markov Property)
Because the covariance decays as $C(r) = C(0) z^{|r|}$, the stationary process is a first-order spatial autoregressive process, AR(1). The conditional distribution of $x_j$ given the entire remaining network depends only on its immediate boundaries $\{x_{j-1}, x_{j+1}\}$:
$$P(x_j \mid \{x_k\}_{k \neq j}) = P(x_j \mid x_{j-1}, x_{j+1})$$

The bilateral predictor is $\hat{x}_j = \beta_1 x_{j-1} + \beta_2 x_{j+1}$. Using the covariance matrix of $(x_{j-1}, x_j, x_{j+1})^T$:
$$\Sigma = C(0) \begin{pmatrix} 1 & z & z^2 \\ z & 1 & z \\ z^2 & z & 1 \end{pmatrix}$$

The minimum possible absolute MSE is given by the Schur complement:
$$\text{MSE}_{\text{multi}} = C(0) - C(0)\begin{pmatrix} z & z \end{pmatrix} \begin{pmatrix} 1 & z^2 \\ z^2 & 1 \end{pmatrix}^{-1} \begin{pmatrix} z \\ z \end{pmatrix}$$

Inverting the $2 \times 2$ boundary matrix yields:
$$\text{MSE}_{\text{multi}} = C(0) \left( 1 - \frac{2z^2}{1+z^2} \right) = C(0) \left( \frac{1 - e^{-2/\xi}}{1 + e^{-2/\xi}} \right)$$

Imposing the condition $\text{MSE}_{\text{multi}} \le \delta$ establishes the lower bound:
$$\delta \ge \delta_{\min}^{(2)} = C(0) \left( \frac{1 - e^{-2/\xi}}{1 + e^{-2/\xi}} \right)$$

---

### File 3: `continuous_spde.md`

# Continuous SPDE Generalization & Hilbert Space Optimization

This document transitions our predictability model from a discrete lattice to continuous infinite-dimensional spaces, establishing the mathematical foundations for continuous prediction horizons.

---

## The Continuous Spatial Limit

By letting the lattice spacing $\Delta x \to 0$ and keeping the continuous diffusion rate $D = J (\Delta x)^2$ constant, the discrete system converges to the stochastic heat equation with additive space-time white noise $\dot{W}(x, t)$:

$$\frac{\partial u(x, t)}{\partial t} = -\alpha u(x, t) + D \frac{\partial^2 u(x, t)}{\partial x^2} + \sigma \dot{W}(x, t)$$

Using the abstract framework of Da Prato and Zabczyk, we model this as a stochastic evolution equation on the Hilbert space $H = L^2(\mathbb{R})$:
$$dU(t) = A U(t) dt + B dW(t)$$
where $A = D \frac{\partial^2}{\partial x^2} - \alpha I$ generates a strongly continuous semigroup.

### Continuous Stationary Covariance
The stationary spatial covariance operator $Q$ has a kernel representing the exact continuous exponential decay:
$$C(x, y) = \mathbb{E}[u(x, \infty) u(y, \infty)] = C(0) e^{-|x-y|/\xi}$$
where the continuous spatial correlation length is $\xi = \sqrt{D/\alpha}$ and $C(0) = \frac{\sigma^2}{4\sqrt{\alpha D}}$.

---

## Hilbert Space Optimization of Linear Predictors

Because $L^2(\Omega)$ is a real Hilbert space, the optimal linear estimator of a field variable $u(x)$ using boundary observations is the orthogonal projection.

### 1. Unilateral Continuous Horizon
The optimal estimator of $u(x)$ using a single point $u(y)$ is $\hat{u}(x) = \beta u(y)$. The projection theorem guarantees that the minimum error satisfies:
$$\text{MSE}_{\text{uni}}(r) = \big\| u(x) - e^{-r/\xi} u(y) \big\|^2 = C(0) \left( 1 - e^{-2r/\xi} \right)$$
where $r = |x-y|$.

### 2. Bilateral Continuous Horizon
For $a < x < b$, the optimal predictor using the boundary $\{u(a), u(b)\}$ is:
$$P = \beta_1 u(a) + \beta_2 u(b)$$

We formally verify in Lean 4 that the prediction error vector $(u(x) - P)$ is orthogonal to the boundary generators:
$$\langle u(x) - P, u(a) \rangle = 0 \quad \text{and} \quad \langle u(x) - P, u(b) \rangle = 0$$

Solving this system yields the continuous bilateral predictability limit:
$$\|u(x) - P\|^2 = C(0) \left( \frac{1 - e^{-2(x-a)/\xi} - e^{-2(b-x)/\xi} + e^{-2(b-a)/\xi}}{1 - e^{-2(b-a)/\xi}} \right)$$

---

## Formal lean 4 Structural Verification

These algebraic structures are verified under classical Hilbert space foundations (`[propext, Classical.choice, Quot.sound]`). The continuous unilateral predictability is formalized as:

```lean
theorem continuous_unilateral_optimal_mse (u : ℝ → E) (C0 z : ℝ)
    (h_cov : ContinuousCovariance u C0 z) (hz0 : 0 < z) (x y : ℝ) (r : ℝ) (hr : |x - y| = r) :
    let β_opt := z ^ r
    ‖u x - β_opt • u y‖^2 = C0 * (1 - z ^ (2 * r))
```

And the continuous spatial Markov boundary projection is verified via:

```lean
theorem continuous_bilateral_optimal_mse (u : ℝ → E) (C0 z : ℝ)
    (h_cov : ContinuousCovariance u C0 z) (hz0 : 0 < z) (hz1 : z < 1)
    (a x b : ℝ) (hax : a < x) (hxb : x < b) :
    ‖u x - (((z ^ (x - a) - z ^ ((b - x) + (b - a))) / (1 - z ^ (2 * (b - a)))) • u a +
             ((z ^ (b - x) - z ^ ((x - a) + (b - a))) / (1 - z ^ (2 * (b - a)))) • u b)‖^2 =
    C0 * ((1 - z ^ (2 * (x - a)) - z ^ (2 * (b - x)) + z ^ (2 * (b - a))) / (1 - z ^ (2 * (b - a))))
```


---

### File 4: `motion_entropy.md`

# Motion as an Entropic Gradient

This document outlines the dynamical extension of our framework, translating informational predictability constraints into physical forces and coordinate attraction.

---

## 1. The Self-Predictability Bias

An active system (or stable localized fluctuation) must maintain its structural integrity and predictability relative to its environment. Under the *Free Energy Principle*, this is modeled as minimizing its local prediction error (surprisal).

Using the continuous unilateral predictability error derived from our Gaussian process:
$$\text{MSE}_{\text{uni}}(r) = C(0) \big(1 - e^{-2r/\xi}\big)$$

Because the underlying noise is Gaussian, the Shannon differential entropy of this prediction error is:
$$H(r) = \frac{1}{2} \ln \Big( 2\pi e \cdot \text{MSE}_{\text{uni}}(r) \Big) = \frac{1}{2} \ln \Big( 2\pi e C(0) \big(1 - e^{-2r/\xi}\big) \Big)$$

We define the **Informational Potential Energy** $V(r)$ of a state positioned at distance $r$ as:
$$V(r) = \gamma H(r) = \frac{\gamma}{2} \ln \Big( 2\pi e C(0) \big(1 - e^{-2r/\xi}\big) \Big)$$
where $\gamma > 0$ is a coupling constant translating information (nats) to mechanical work.

---

## 2. Derivation of the Entropic Force

If a state undergoes motion driven to minimize its prediction entropy (gradient flow), it experiences an effective **entropic force** $F_{\text{entropic}}$ pulling it toward coordinates of higher predictability ($r \to 0$):

$$F_{\text{entropic}}(r) = -\nabla_r V(r) = -\frac{\partial V}{\partial r}$$

Differentiating $V(r)$ with respect to $r$:
$$\frac{\partial V}{\partial r} = \frac{\gamma}{2} \cdot \frac{\partial}{\partial r} \ln \big(1 - e^{-2r/\xi}\big) = \frac{\gamma}{2} \cdot \frac{\frac{2}{\xi} e^{-2r/\xi}}{1 - e^{-2r/\xi}}$$

Simplifying this expression:
$$F_{\text{entropic}}(r) = -\frac{\gamma}{\xi} \frac{e^{-2r/\xi}}{1 - e^{-2r/\xi}} = -\frac{\gamma}{\xi} \frac{1}{e^{2r/\xi} - 1}$$

---

## 3. Physical Analysis of the Force

```
  Force (F)
    ^
    |          |
    |          |
    |          |  <- Short-Range: F ≈ -γ / (2r)  [Gravitational Scaling]
    |         /
    |       /
----+---------------------> Distance (r)
    |     /
    |   /
    | /           <- Long-Range: Exponential decay
    |
```

### Attractive Restoring Behavior
Because $\gamma > 0$ and $\xi > 0$, we have $F_{\text{entropic}}(r) < 0$ for all $r > 0$. The entropic gradient always acts as an attractive force pulling the state back toward its baseline prediction reference coordinate.

### Short-Range Limit ($r \ll \xi$)
When the state is close to its reference point compared to the environmental correlation scale ($\xi$), we Taylor expand the exponential term ($e^{2r/\xi} \approx 1 + \frac{2r}{\xi}$):
$$F_{\text{entropic}}(r) \approx -\frac{\gamma}{\xi} \frac{1}{\left(1 + \frac{2r}{\xi}\right) - 1} = -\frac{\gamma}{2r}$$

This is an exact physical match for **gravitational scaling** in lower dimensions:
* In $d$-dimensional space, gravitational force scales as $\frac{1}{r^{d-1}}$ (from Gauss's law).
* On our continuous line ($d=1$, moving in a 2D-like logarithmic potential field), the entropic force scales as **$\frac{1}{r}$**.

At short ranges, the local self-predictability gradient generates an emergent attractive force identical to gravitational attraction.

---

## 4. Formalization in Lean 4

This dynamical system is formalized in `motion.lean` using a directional, coordinate-aware entropic force field $F(x)$ where $r = |x|$:

$$F_{\text{entropic}}(x) = -\text{sign}(x) \frac{\gamma}{\xi} \frac{1}{e^{2|x|/\xi} - 1}$$

This is verified to be strictly attractive and dissipative via:

```lean
theorem entropic_force_attractive (γ ξ x : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ) :
    x * entropic_force γ ξ x ≤ 0
```

We define a **Self-Correcting Actor** as a trajectory that asymptotically converges to perfect predictability, minimizing its local entropy under this flow:

```lean
structure Actor (γ ξ dt : ℝ) where
  x0 : ℝ                  
  pos : ℕ → ℝ             
  is_trajectory : ∀ n, pos (n + 1) = step_motion γ ξ dt (pos n)
  self_corrects : ∀ ε > 0, ∃ N, ∀ n ≥ N, |pos n| < ε
```

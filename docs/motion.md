
# Motion as an Entropic Gradient

This document outlines the dynamical laws of our framework, translating informational predictability constraints into physical forces and coordinate attraction.

---

## 1. Informational Potential Energy

Under the *Free Energy Principle*, a localized active system must maintain its structural integrity and predictability relative to its environment by minimizing its local prediction error.

Using the continuous unilateral predictability error (MSE) derived in our framework:
$$\text{MSE}_{\text{uni}}(r) = C_0 \big(1 - e^{-2r/\xi}\big)$$

Because the underlying noise is Gaussian, the Shannon differential entropy of this prediction error is:
$$H(r) = \frac{1}{2} \ln \Big( 2\pi e \cdot \text{MSE}_{\text{uni}}(r) \Big) = \frac{1}{2} \ln \Big( 2\pi e C_0 \big(1 - e^{-2r/\xi}\big) \Big)$$

Ignoring constant offsets, we define the **Informational Potential Energy** $V(r)$ of a state positioned at distance $r$ as:
$$V(r) = \frac{\gamma}{2} \ln \big(C_0(1 - e^{-2r/\xi})\big)$$
where $\gamma > 0$ is a coupling constant translating information (nats) to mechanical work.

---

## 2. Derivation of the Entropic Force

If a state is driven to minimize its prediction entropy (undergoing gradient flow), it experiences an effective **entropic force** pulling it toward coordinates of higher predictability ($r \to 0$):

$$F_{\text{entropic}}(r) = -\frac{\partial V}{\partial r} = -\frac{\gamma}{\xi} \frac{1}{e^{2r/\xi} - 1}$$

We formalize this directional, coordinate-aware force in Lean 4 as:
```lean
def entropic_force (γ ξ x : ℝ) : ℝ :=
  if x = 0 then 0
  else if x > 0 then - (γ / ξ) * (1 / (exp (2 * x / ξ) - 1))
  else (γ / ξ) * (1 / (exp (2 * (-x) / ξ) - 1))
```

We prove that this force field is strictly dissipative and attractive (pulling states back to their reference coordinates):
```lean
theorem entropic_force_attractive (γ ξ x : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ) :
    x * entropic_force γ ξ x ≤ 0
```

---

## 3. Physical Limits of the Force

### Short-Range Limit ($r \ll \xi$)
When a state is close to its reference coordinate, we Taylor expand the exponential term ($e^{2r/\xi} \approx 1 + \frac{2r}{\xi}$):
$$F_{\text{entropic}}(r) \approx -\frac{\gamma}{\xi} \frac{1}{\left(1 + \frac{2r}{\xi}\right) - 1} = -\frac{\gamma}{2r}$$

This recovers **gravitational scaling** in lower dimensions ($1/r$). At short ranges, local self-predictability gradients generate an emergent attractive force identical to physical gravity.

### Long-Range Limit ($r \gg \xi$)
At long ranges, the exponential term dominates, and the force decays exponentially to zero:
$$F_{\text{entropic}}(r) \approx -\frac{\gamma}{\xi} e^{-2r/\xi}$$

---

## 4. Multi-Body Gravitational Dynamics

We extend this model to multi-body coordinate systems by defining the mutual entropic force exerted on a coordinate $x_1$ by another coordinate $x_2$:
```lean
def mutual_force (γ ξ x1 x2 : ℝ) : ℝ :=
  entropic_force γ ξ (x1 - x2)
```

We formally prove that this mutual force satisfies **Newton's Third Law** (equal and opposite reactions) and decays monotonically as physical distance increases:

```lean
theorem mutual_force_symmetric (γ ξ x1 x2 : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ) :
    mutual_force γ ξ x1 x2 = - mutual_force γ ξ x2 x1

theorem mutual_force_monotone (γ ξ r1 r2 : ℝ) (hγ : 0 < γ) (hξ : 0 < ξ)
    (hr1 : 0 < r1) (hr2 : r1 < r2) :
    |entropic_force γ ξ r2| < |entropic_force γ ξ r1|
```

We verify that the entropic force is a conservative potential field by proving that it matches the negative derivative of the informational potential:
```lean
theorem mutual_potential_gradient {T : Type*} [MetricSpace T] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : ExponentialCovarianceProcess T E) (γ ξ : ℝ) ...
    HasDerivAt U (- mutual_force γ ξ x1 x2) x1
```

---

## 5. Discrete Dynamics & Self-Correcting Actors

Under discrete temporal updates ($x_{t+1} = x_t + \Delta t \cdot F(x_t)$), we define a **Self-Correcting Actor** as an agent trajectory that asymptotically minimizes its local prediction entropy, converging to its reference coordinate under this entropic flow:

```lean
structure Actor (γ ξ dt : ℝ) where
  x0 : ℝ
  pos : ℕ → ℝ
  is_trajectory : ∀ n, pos (n + 1) = step_motion γ ξ dt (pos n)
  self_corrects : ∀ ε > 0, ∃ N, ∀ n ≥ N, |pos n| < ε
```
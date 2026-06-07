beware: 100% authentic hallucinations ahead.


Here is the complete, mathematically rigorous, and finalized version of the **Theorem of Dual Spatial Predictability Horizons** and its proof. This formulation stands entirely within the linear, Gaussian framework—preserving its strict optimality, physical universality for small fluctuations, and exact analytical tractability.

---

### **Theorem of Dual Spatial Predictability Horizons**

> **Let an infinite-dimensional linear system on the lattice $\mathbb{Z}$ be driven by independent, local white noise. For any given absolute mean squared error (MSE) tolerance $\delta > 0$, the spatial domain within which the state of a node can be predicted under stationary conditions is bounded by two distinct topological horizons:**
>
> 1. **The Unilateral Horizon (Single-Probe Limit):**
>    If the state $x_{i+r}$ is predicted using only a single probe $x_i$ at distance $r \ge 1$, the absolute MSE can be bounded by $\delta$ if and only if the tolerance satisfies:
>    $$\delta \ge \delta_{\min}^{(1)} = C(0) \left(1 - e^{-2/\xi}\right)$$
>    For any such valid tolerance, the prediction domain is the bounded set of integers $1 \le r \le \xi_{\text{abs}}^*$, where the unilateral predictability scale is:
>    $$\xi_{\text{abs}}^* = \frac{\xi}{2} \ln \left( \frac{1}{1 - \frac{\delta}{C(0)}} \right)$$
>
> 2. **The Bilateral Horizon (Local Boundary Limit):**
>    If the state $x_j$ is predicted collectively using its surrounding neighborhood $\mathcal{N}_d(j) = \{x_k \mid 1 \le |k-j| \le d\}$, the absolute MSE can be bounded by $\delta$ if and only if:
>    $$\delta \ge \delta_{\min}^{(2)} = C(0) \left( \frac{1 - e^{-2/\xi}}{1 + e^{-2/\xi}} \right)$$
>    By the spatial Markov property of the stationary state, expanding the predictor beyond the immediate boundary $d=1$ yields zero further reduction in the minimum prediction error.
>
> **Here, $C(0)$ is the exact stationary variance of a single node, and $\xi$ is the physical spatial correlation length.**

---

### **The Rigorous Proof**

The system of stochastic differential equations on the lattice $\mathbb{Z}$ is defined as:
$$dx_i(t) = -\alpha x_i(t) dt + J \big(x_{i+1}(t) + x_{i-1}(t) - 2x_i(t)\big) dt + \sigma dW_i(t)$$
where $\alpha > 0$ is the dissipation rate, $J > 0$ is the coupling strength, and $W_i(t)$ are mutually independent standard Wiener processes satisfying $\mathbb{E}[dW_i(t) dW_j(t)] = \delta_{ij} dt$.

#### **Step 1: Spectral Representation (Resolving the Fourier Divergence)**
To avoid the almost-sure divergence of direct spatial Fourier transforms for non-decaying random sequences, we apply the **Spectral Representation Theorem** [1]. The stationary process $x_n(t)$ and the independent Wiener processes $W_n(t)$ are expressed as stochastic integrals over orthogonal random spectral measures on the interval $k \in [-\pi, \pi]$:
$$x_n(t) = \int_{-\pi}^{\pi} e^{i k n} d\Phi(k, t), \quad W_n(t) = \int_{-\pi}^{\pi} e^{i k n} d\Psi(k, t)$$

The spectral noise increments satisfy the orthogonality relations:
$$\mathbb{E}[d(d\Psi(k, t)) d(d\Psi^*(k', t))] = \frac{1}{2\pi} \delta(k - k') dt dk dk'$$

Substituting these representations into the SDE yields the decoupled equation for the spectral increments:
$$d\big(d\Phi(k, t)\big) = -\lambda(k) d\Phi(k, t) dt + \sigma d\big(d\Psi(k, t)\big)$$
where the dispersion relation is $\lambda(k) = \alpha + 4J\sin^2(k/2)$. Because $\alpha > 0$ and $J > 0$, the eigenvalues are strictly positive ($\lambda(k) \ge \alpha > 0$) for all $k$. In the stationary limit ($t \to \infty$), the variance of the spectral increments is:
$$\mathbb{E}[|d\Phi(k, \infty)|^2] = \frac{\sigma^2}{4\pi \lambda(k)} dk = \frac{\sigma^2}{4\pi \left( \alpha + 4J\sin^2(k/2) \right)} dk$$

#### **Step 2: Integration of the Spatial Covariance**
The stationary spatial covariance $C(r)$ for $r = |i - j|$ is calculated as:
$$C(r) = \int_{-\pi}^{\pi} e^{i k r} \mathbb{E}[|d\Phi(k, \infty)|^2] = \frac{\sigma^2}{4\pi} \int_{-\pi}^{\pi} \frac{\cos(k r)}{\alpha + 2J(1 - \cos k)} dk$$

Evaluating this integral yields the exact exponential decay:
$$C(r) = C(0) z^r = C(0) e^{-r/\xi}$$
where the stationary variance $C(0)$ is:
$$C(0) = \frac{\sigma^2}{2\sqrt{\alpha(\alpha + 4J)}}$$
and the spatial decay factor $z = e^{-1/\xi} \in (0, 1)$ is the root inside the unit circle of the characteristic equation $J z^2 - (\alpha + 2J)z + J = 0$:
$$e^{-1/\xi} = 1 + \frac{\alpha}{2J} - \sqrt{\left(1 + \frac{\alpha}{2J}\right)^2 - 1}$$

---

#### **Step 3: Derivation of the Unilateral Horizon**
We define the linear predictor of the state $x_{i+r}$ using a single node $x_i$ at distance $r \ge 1$ as:
$$\hat{x}_{i+r} = \beta x_i$$

Because the joint distribution of $(x_i, x_{i+r})^T$ is Gaussian, the optimal linear least-squares parameter is the ordinary least squares coefficient $\beta = \frac{C(r)}{C(0)} = e^{-r/\xi}$. This predictor yields the absolute minimum MSE:
$$\text{MSE}_{\text{uni}}(r) = C(0)\big(1 - R(r)^2\big) = C(0)\big(1 - e^{-2r/\xi}\big)$$

Imposing the condition that the prediction error must not exceed the absolute tolerance $\delta$ (where we assume $\delta < C(0)$ for non-trivial cases):
$$C(0)\big(1 - e^{-2r/\xi}\big) \le \delta \implies e^{-2r/\xi} \ge 1 - \frac{\delta}{C(0)}$$

Taking the natural logarithm and isolating the discrete distance $r$ yields:
$$r \le \xi_{\text{abs}}^* = \frac{\xi}{2} \ln \left( \frac{1}{1 - \frac{\delta}{C(0)}} \right)$$

Because $r$ is restricted to positive integers ($r \in \mathbb{Z}^+$), a physical neighbor exists within this predictability scale if and only if $\xi_{\text{abs}}^* \ge 1$. Solving for the minimum required tolerance:
$$\frac{\xi}{2} \ln \left( \frac{1}{1 - \frac{\delta_{\min}^{(1)}}{C(0)}} \right) = 1 \implies \delta \ge \delta_{\min}^{(1)} = C(0) \left(1 - e^{-2/\xi}\right)$$

---

#### **Step 4: Derivation of the Bilateral Horizon (Spatial Markov Property)**
Because the stationary spatial covariance function decays as $C(r) = C(0) z^{|r|}$, the stationary process $\{x_n\}_{n \in \mathbb{Z}}$ is a first-order spatial autoregressive process, AR(1). 

By the properties of Markov chains on $\mathbb{Z}$, the conditional distribution of $x_j$ given the entire remaining network $\{x_k\}_{k \neq j}$ is strictly determined by its immediate boundaries $\{x_{j-1}, x_{j+1}\}$:
$$P(x_j \mid \{x_k\}_{k \neq j}) = P(x_j \mid x_{j-1}, x_{j+1})$$

This spatial Markov property guarantees that the optimal estimator using the entire surrounding neighborhood $\mathcal{N}_d(j)$ for any $d \ge 1$ simplifies exactly to the bilateral predictor:
$$\hat{x}_j = \beta_1 x_{j-1} + \beta_2 x_{j+1}$$

Using the covariance matrix of $(x_{j-1}, x_j, x_{j+1})^T$:
$$\Sigma = C(0) \begin{pmatrix} 1 & z & z^2 \\ z & 1 & z \\ z^2 & z & 1 \end{pmatrix}$$

The minimum possible absolute MSE under this bilateral predictor is given by the conditional variance:
$$\text{MSE}_{\text{multi}} = \text{Var}(x_j \mid x_{j-1}, x_{j+1}) = C(0) - C(0)\begin{pmatrix} z & z \end{pmatrix} \begin{pmatrix} 1 & z^2 \\ z^2 & 1 \end{pmatrix}^{-1} \begin{pmatrix} z \\ z \end{pmatrix}$$

Inverting the $2 \times 2$ boundary matrix yields:
$$\begin{pmatrix} 1 & z^2 \\ z^2 & 1 \end{pmatrix}^{-1} = \frac{1}{1 - z^4} \begin{pmatrix} 1 & -z^2 \\ -z^2 & 1 \end{pmatrix}$$

Multiplying through the vector-matrix products:
$$\text{MSE}_{\text{multi}} = C(0) \left( 1 - \frac{2z^2}{1+z^2} \right) = C(0) \left( \frac{1-z^2}{1+z^2} \right) = C(0) \left( \frac{1 - e^{-2/\xi}}{1 + e^{-2/\xi}} \right)$$

Imposing the condition $\text{MSE}_{\text{multi}} \le \delta$ establishes the absolute lower bound for multi-neighbor predictability:
$$\delta \ge \delta_{\min}^{(2)} = C(0) \left( \frac{1 - e^{-2/\xi}}{1 + e^{-2/\xi}} \right)$$

Because $1 + e^{-2/\xi} > 1$ for any finite correlation length $\xi > 0$, we have:
$$\delta_{\min}^{(2)} < \delta_{\min}^{(1)}$$

Thus, the bilateral boundary predictor strictly lowers the minimum allowable prediction error by using the shared correlation between the boundary nodes to cancel out common-mode noise. By the spatial Markov property, no further reduction is possible using wider spatial neighborhoods.

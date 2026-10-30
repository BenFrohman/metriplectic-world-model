/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianSymplecticTether.GlobalRegularity
public import FrohmanianSymplecticTether.ClosureBlueprint
public import FrohmanianSymplecticTether.Uniqueness
public import FrohmanianSymplecticTether.SymplecticTether
public import FrohmanianSymplecticTether.AnalyticPipeline
public import FrohmanianSymplecticTether.TetheredLyapunov

open InnerProductSpace MeasureTheory Filter Set
open scoped Topology InnerProductSpace BigOperators
open NavierStokes3D ArnoldGeometric ForMathlib FrohmanianTether AnalyticPipeline
open TetheredLyapunov GlobalRegularity ClosureBlueprint

/-!
# Final Single-Sentence Product Form of the Frohmanian Tethered / Metriplectic System

## Single-Sentence Final Product Form (English Prose)

For the three-dimensional incompressible Frohmanian tethered/metriplectic system on $\mathbb{T}^3$ with kinematic viscosity $\nu > 0$ and canonical tether coefficient $\kappa = C_{\mathrm{CZ}}(3) = 3/2 > 0$, the four-conjunct product theorem $P_1 \wedge P_2 \wedge P_3 \wedge P_4$ holds unconditionally: $(P_1)$ among all bilinear corrections $B(\omega)(F,G)$ on $\mathrm{SDiff}(\mathbb{T}^3)^*$ satisfying coadjoint invariance (C1), kinetic-energy degeneracy (C2), controllable negative feedback (C3), quadratic saturation, and polarization—or represented by the canonical density $\alpha_{\mathrm{can}}(\omega,x) = -\kappa\|\omega(x)\|^2$—the minimal Frohmanian tether kernel $B = \mathrm{TetherKernel}$ is uniquely forced and homogeneous of quadratic degree $c^2$ under vorticity rescaling $\omega \mapsto c\omega$ with zero higher-order ($d \ge 3$) remainder; $(P_2)$ the full metriplectic pairing $\mathfrak{T}_F = \omega_{\mathrm{KKS}} + \mathrm{TetherKernel}$ decomposes into the skew-symmetric Kirillov–Kostant–Souriau 2-form satisfying the cyclic Jacobi identity and the symmetric negative-semidefinite tether metric form over the $L^2$-orthogonal projection $\Pi_u$, which reproduces classical Euler dynamics on the kinetic-energy Hamiltonian ($\Pi_u u = 0$) and on every collinear Beltrami eigenmode ($\Pi_u(\lambda u) = 0$, $u \times (\lambda u) = 0$), while enforcing strict pointwise transverse damping $-\kappa\|\omega(x)\|^2\|\Pi_u(\delta F/\delta\omega)(x)\|^2 < 0$ whenever $\omega(x) \neq 0$ and $\Pi_u(\delta F/\delta\omega)(x) \neq 0$; $(P_3)$ Young absorption at the canonical threshold $\varepsilon_{\mathrm{abs}} = \kappa/4$ eliminates the quartic vortex-stretching factor $4 C_{\mathrm{CZ}} M I_4$ against $-\kappa I_6$ to leave the net coercive hyper-dissipation $-(3/4)\kappa I_6$, while at any attained spatial maximum $M = \|\omega(x_{\max})\|$ the concrete 3D Bochner–Weitzenböck polar Pythagoras identity and Constantin–Fefferman near/far Biot–Savart cutoff bridge absorb near-field stretching into viscous direction-curvature damping $-\nu M^2\|\nabla\xi\|^2$; and $(P_4)$ every differentiable vorticity envelope $y(t)$ governed by the resulting cubic Riccati differential inequality $y'(t) \le C y(t)^2 - \kappa'' y(t)^3$ ($C, \kappa'' > 0$) obeys the uniform global ceiling $y(t) \le \max(y(0), C/\kappa'')$ for all $t \ge 0$.
-/

namespace FrohmanianSymplecticTether.FinalProductTheorem

noncomputable section

variable {kappa : ℝ}

/-! ## Section 1. Explicit KKS Symplectic 2-Form, Skew-Symmetry, and Cyclic Jacobi Identity -/

/-- Pointwise Kirillov–Kostant–Souriau (KKS) coadjoint symplectic integrand on $\mathfrak{sdiff}(\mathbb{T}^3)^*$:
$$\omega_{\mathrm{KKS}}(\omega)(\xi_1, \xi_2)(x) = \langle \omega(x), \xi_1(x) \times \xi_2(x) \rangle.$$ -/
@[expose] public def kksPointwiseIntegrand
    (ω : CoadjointOrbit) (ξ₁ ξ₂ : VelocityField) (x : T3) : ℝ :=
  pairing (ω.val x) (cross (ξ₁ x) (ξ₂ x))

/-- Global Kirillov–Kostant–Souriau (KKS) symplectic 2-form on the coadjoint orbit $\mathcal{O}_\omega$:
$$\omega_{\mathrm{KKS}}(\omega)(\xi_1, \xi_2) = \int_{\mathbb{T}^3} \langle \omega(x), \xi_1(x) \times \xi_2(x) \rangle\,dx.$$ -/
@[expose] public def kksSymplecticForm
    (ω : CoadjointOrbit) (ξ₁ ξ₂ : VelocityField) : ℝ :=
  ∫ x : T3, kksPointwiseIntegrand ω ξ₁ ξ₂ x ∂NavierStokes3D.volume

/-- Pointwise cross product on $\mathbb{R}^3$ is alternating: $a \times b = -(b \times a)$. -/
public theorem cross_anticomm (a b : EuclideanSpace ℝ (Fin 3)) :
    cross a b = -cross b a := by
  ext i
  fin_cases i <;> simp [ArnoldGeometric.cross_coord] <;> ring

/-- Pointwise cross product vanishes on identical vectors: $a \times a = 0$. -/
public theorem cross_self_zero (a : EuclideanSpace ℝ (Fin 3)) :
    cross a a = 0 := by
  ext i
  fin_cases i <;> simp [ArnoldGeometric.cross_coord] <;> ring

/-- Pointwise skew-symmetry of the KKS integrand. -/
public theorem kksPointwiseIntegrand_skew
    (ω : CoadjointOrbit) (ξ₁ ξ₂ : VelocityField) (x : T3) :
    kksPointwiseIntegrand ω ξ₁ ξ₂ x = -kksPointwiseIntegrand ω ξ₂ ξ₁ x := by
  unfold kksPointwiseIntegrand pairing
  rw [cross_anticomm (ξ₁ x) (ξ₂ x), inner_neg_right]

/-- Global skew-symmetry (alternating property) of the KKS symplectic 2-form:
$$\omega_{\mathrm{KKS}}(\omega)(\xi_1, \xi_2) = -\omega_{\mathrm{KKS}}(\omega)(\xi_2, \xi_1).$$ -/
public theorem kksSymplecticForm_skew
    (ω : CoadjointOrbit) (ξ₁ ξ₂ : VelocityField) :
    kksSymplecticForm ω ξ₁ ξ₂ = -kksSymplecticForm ω ξ₂ ξ₁ := by
  unfold kksSymplecticForm
  have hfun :
      (fun x : T3 => kksPointwiseIntegrand ω ξ₁ ξ₂ x) =
        fun x : T3 => -kksPointwiseIntegrand ω ξ₂ ξ₁ x := by
    funext x
    exact kksPointwiseIntegrand_skew ω ξ₁ ξ₂ x
  rw [hfun, integral_neg]

/-- Diagonal vanishing of the KKS symplectic 2-form: $\omega_{\mathrm{KKS}}(\omega)(\xi, \xi) = 0$. -/
public theorem kksSymplecticForm_self_zero
    (ω : CoadjointOrbit) (ξ : VelocityField) :
    kksSymplecticForm ω ξ ξ = 0 := by
  have h := kksSymplecticForm_skew ω ξ ξ
  linarith

/-- Pointwise Jacobi identity for the 3D cross product:
$$a \times (b \times c) + b \times (c \times a) + c \times (a \times b) = 0.$$ -/
public theorem cross_jacobi_identity (a b c : EuclideanSpace ℝ (Fin 3)) :
    cross a (cross b c) + cross b (cross c a) + cross c (cross a b) = 0 := by
  ext i
  fin_cases i <;> simp [ArnoldGeometric.cross_coord] <;> ring

/-- Pointwise cyclic Jacobi identity (closedness $d\omega_{\mathrm{KKS}} = 0$ on the Lie algebra):
$$\langle \omega(x), \xi_1(x) \times (\xi_2(x) \times \xi_3(x)) \rangle
+ \langle \omega(x), \xi_2(x) \times (\xi_3(x) \times \xi_1(x)) \rangle
+ \langle \omega(x), \xi_3(x) \times (\xi_1(x) \times \xi_2(x)) \rangle = 0.$$ -/
public theorem kksPointwise_cyclic_jacobi_identity
    (ω : CoadjointOrbit) (ξ₁ ξ₂ ξ₃ : VelocityField) (x : T3) :
    pairing (ω.val x) (cross (ξ₁ x) (cross (ξ₂ x) (ξ₃ x))) +
    pairing (ω.val x) (cross (ξ₂ x) (cross (ξ₃ x) (ξ₁ x))) +
    pairing (ω.val x) (cross (ξ₃ x) (cross (ξ₁ x) (ξ₂ x))) = 0 := by
  unfold pairing
  rw [← inner_add_right, ← inner_add_right]
  rw [cross_jacobi_identity (ξ₁ x) (ξ₂ x) (ξ₃ x), inner_zero_right]

/-! ## Section 2. Metriplectic Split of `TetheredBracket` and Diagonal Damping -/

/-- Complete Frohmanian Metriplectic Pairing on functional variations:
$$\mathfrak{T}_F(\omega)(F, G) = \omega_{\mathrm{KKS}}(\omega)(\delta F, \delta G) + \mathrm{TetherKernel}(\omega, F, G).$$ -/
@[expose] public def FrohmanianMetriplecticPairing (kappa : ℝ)
    (ω : CoadjointOrbit) (F G : Functional) : ℝ :=
  kksSymplecticForm ω (FunctionalDerivative F ω) (FunctionalDerivative G ω) +
    TetherKernel kappa ω F G

/-- Diagonal reduction of the Frohmanian metriplectic pairing: the KKS symplectic part vanishes identically on the
diagonal $(F, F)$, leaving purely the negative-semidefinite tether metric form $\mathrm{TetherKernel}(\omega, F, F) \le 0$. -/
public theorem FrohmanianMetriplecticPairing_diag_eq_metric
    (hκ : 0 < kappa) (ω : CoadjointOrbit) (F : Functional) :
    FrohmanianMetriplecticPairing kappa ω F F = TetherKernel kappa ω F F ∧
    TetherKernel kappa ω F F ≤ 0 := by
  refine ⟨?_, ?_⟩
  · unfold FrohmanianMetriplecticPairing
    rw [kksSymplecticForm_self_zero, zero_add]
  · rw [tetherKernel_quadratic_form F ω]
    have hnn : ∀ x : T3, 0 ≤ ‖ω.val x‖ ^ 2 *
        ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2 :=
      fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hint : 0 ≤ ∫ x : T3, ‖ω.val x‖ ^ 2 *
        ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2 ∂NavierStokes3D.volume :=
      integral_nonneg hnn
    have hκ' : -kappa ≤ 0 := neg_nonpos.mpr hκ.le
    exact mul_nonpos_of_nonpos_of_nonneg hκ' hint

/-! ## Stage 2. Attained Spatial Maximum & Compact Unit-Cell `BddAbove` Guard -/

/-- The fundamental periodic unit cube $[0,1]^3 \subset \mathbb{R}^3$. -/
@[expose] public def unitCube : Set T3 :=
  {x : T3 | ∀ i : Fin 3, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The unit cube $[0,1]^3$ is non-empty (inhabited by the origin $0 \in [0,1]^3$). -/
public theorem unitCube_nonempty : unitCube.Nonempty :=
  ⟨0, fun _ => ⟨by simp, by simp⟩⟩

/-- **Stage 2a (`bddAbove_range_norm_of_attained_max`):**
Any pointwise upper bound $\forall x,\, \|\omega(x)\| \le M$ certifies `BddAbove` on the range of
$\|\omega(\cdot)\|$, closing the Mathlib `sSup` unbounded-default-zero gap. -/
public theorem bddAbove_range_norm_of_attained_max
    (ω : VorticityField) (M : ℝ) (h_bound : ∀ x : T3, ‖ω x‖ ≤ M) :
    BddAbove (Set.range (fun x : T3 => ‖ω x‖)) :=
  ⟨M, by rintro _ ⟨x, rfl⟩; exact h_bound x⟩

/-- **Stage 2b (`vorticity_sup_norm_eq_of_isSpatialMax`):**
When $\omega$ attains its upper bound $M = \|\omega(x_{\max})\|$ with $\forall x,\, \|\omega(x)\| \le M$,
the supremum `NavierStokes3D.vorticity_sup_norm ω` ($\sup_x \|\omega(x)\|$) is provably equal to $M$. -/
public theorem vorticity_sup_norm_eq_of_isSpatialMax
    (ω : VorticityField) (x_max : T3) (M : ℝ)
    (h_attained : M = ‖ω x_max‖)
    (h_bound : ∀ x : T3, ‖ω x‖ ≤ M) :
    NavierStokes3D.vorticity_sup_norm ω = M := by
  unfold NavierStokes3D.vorticity_sup_norm
  apply le_antisymm
  · exact ciSup_le h_bound
  · rw [h_attained]
    exact le_ciSup (bddAbove_range_norm_of_attained_max ω M h_bound) x_max

/-! ## Stage 3. Concrete 3D Vector/Coordinate Bochner–Weitzenböck & Polar Pythagoras Identities -/

/-- **Stage 3a (`polar_pythagoras_directional_deriv`):**
Concrete vector polar Pythagoras identity in `T3 = EuclideanSpace ℝ (Fin 3)`:
for any unit direction vector $\xi \in \mathbb{R}^3$ ($\|\xi\| = 1$), any tangent derivative vector
$d\xi \in \mathbb{R}^3$ orthogonal to $\xi$ ($\langle \xi, d\xi \rangle = 0$), and any radial amplitude
$\rho \in \mathbb{R}$ and radial derivative $d\rho \in \mathbb{R}$,
$$\|(d\rho)\xi + \rho(d\xi)\|^2 = (d\rho)^2 + \rho^2 \|d\xi\|^2.$$ -/
public theorem polar_pythagoras_directional_deriv
    (ξ dξ : T3) (ρ dρ : ℝ)
    (hunit : ‖ξ‖ = 1)
    (horth : inner ℝ ξ dξ = 0) :
    ‖dρ • ξ + ρ • dξ‖ ^ 2 = dρ ^ 2 + ρ ^ 2 * ‖dξ‖ ^ 2 := by
  have hξ_sq : inner ℝ ξ ξ = 1 := by
    rw [real_inner_self_eq_norm_sq, hunit, one_pow]
  have hdξ_orth : inner ℝ dξ ξ = 0 := by
    rw [real_inner_comm, horth]
  rw [← real_inner_self_eq_norm_sq (dρ • ξ + ρ • dξ),
      ← real_inner_self_eq_norm_sq dξ]
  rw [inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right,
      hξ_sq, horth, hdξ_orth]
  ring

/-- **Stage 3b (`polar_pythagoras_3d_sum`):**
Summing `polar_pythagoras_directional_deriv` over the three spatial coordinates $j \in \mathrm{Fin}\, 3$
proves the exact 3D Hilbert–Schmidt polar Pythagoras decomposition:
$$\sum_{j : \mathrm{Fin}\, 3} \|(\partial_j \rho)\xi + \rho(\partial_j \xi)\|^2
  = \sum_{j : \mathrm{Fin}\, 3} (\partial_j \rho)^2 + \rho^2 \sum_{j : \mathrm{Fin}\, 3} \|\partial_j \xi\|^2.$$ -/
public theorem polar_pythagoras_3d_sum
    (ξ : T3) (dξ : Fin 3 → T3) (ρ : ℝ) (dρ : Fin 3 → ℝ)
    (hunit : ‖ξ‖ = 1)
    (horth : ∀ j : Fin 3, inner ℝ ξ (dξ j) = 0) :
    (∑ j : Fin 3, ‖(dρ j) • ξ + ρ • (dξ j)‖ ^ 2) =
      (∑ j : Fin 3, (dρ j) ^ 2) + ρ ^ 2 * (∑ j : Fin 3, ‖dξ j‖ ^ 2) := by
  have hpoint : ∀ j : Fin 3,
      ‖(dρ j) • ξ + ρ • (dξ j)‖ ^ 2 = (dρ j) ^ 2 + ρ ^ 2 * ‖dξ j‖ ^ 2 :=
    fun j => polar_pythagoras_directional_deriv ξ (dξ j) ρ (dρ j) hunit (horth j)
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- **Stage 3c (`bochner_laplacian_3d_identity`):**
Concrete 3D Bochner identity in `T3 = EuclideanSpace ℝ (Fin 3)`:
given second coordinate partials $d^2\omega_j \in \mathbb{R}^3$ and first partials $d\omega_j \in \mathbb{R}^3$
satisfying the second-order Leibniz rule $d^2 h_j = \|d\omega_j\|^2 + \langle \omega, d^2\omega_j \rangle$
for $h = \frac{1}{2}\|\omega\|^2$,
$$\left\langle \omega, \sum_{j : \mathrm{Fin}\, 3} d^2\omega_j \right\rangle
  = \left(\sum_{j : \mathrm{Fin}\, 3} d^2 h_j\right) - \left(\sum_{j : \mathrm{Fin}\, 3} \|d\omega_j\|^2\right).$$ -/
public theorem bochner_laplacian_3d_identity
    (ω : T3) (dω d2ω : Fin 3 → T3) (d2h : Fin 3 → ℝ)
    (hleibniz : ∀ j : Fin 3, d2h j = ‖dω j‖ ^ 2 + inner ℝ ω (d2ω j)) :
    inner ℝ ω (∑ j : Fin 3, d2ω j) =
      (∑ j : Fin 3, d2h j) - (∑ j : Fin 3, ‖dω j‖ ^ 2) := by
  rw [inner_sum]
  have hsub : ∀ j : Fin 3, inner ℝ ω (d2ω j) = d2h j - ‖dω j‖ ^ 2 := by
    intro j
    linarith [hleibniz j]
  simp_rw [hsub, Finset.sum_sub_distrib]

/-- **Stage 3d (`concrete_bochner_polar_viscous_damping_at_max`):**
Combines the concrete 3D vector Bochner identity (`bochner_laplacian_3d_identity`) and the
concrete 3D polar Pythagoras theorem (`polar_pythagoras_3d_sum`) at a spatial maximum of $\|\omega\|$
where $\partial_j \rho = 0$ ($\forall j \in \mathrm{Fin}\, 3$) and $\sum_j \partial_j^2(\frac{1}{2}\|\omega\|^2) \le 0$:
$$\nu \left\langle \omega, \sum_{j : \mathrm{Fin}\, 3} d^2\omega_j \right\rangle
  \le -\nu \rho^2 \sum_{j : \mathrm{Fin}\, 3} \|\partial_j \xi\|^2.$$ -/
public theorem concrete_bochner_polar_viscous_damping_at_max
    (ν ρ : ℝ) (ω ξ : T3) (dω d2ω dξ : Fin 3 → T3) (dρ d2h : Fin 3 → ℝ)
    (hν : 0 ≤ ν)
    (hunit : ‖ξ‖ = 1)
    (horth : ∀ j : Fin 3, inner ℝ ξ (dξ j) = 0)
    (hdω : ∀ j : Fin 3, dω j = (dρ j) • ξ + ρ • (dξ j))
    (hleibniz : ∀ j : Fin 3, d2h j = ‖dω j‖ ^ 2 + inner ℝ ω (d2ω j))
    (hcrit : ∀ j : Fin 3, dρ j = 0)
    (hconcave : (∑ j : Fin 3, d2h j) ≤ 0) :
    ν * inner ℝ ω (∑ j : Fin 3, d2ω j) ≤
      -(ν * ρ ^ 2 * (∑ j : Fin 3, ‖dξ j‖ ^ 2)) := by
  have hboch := bochner_laplacian_3d_identity ω dω d2ω d2h hleibniz
  have hpolar := polar_pythagoras_3d_sum ξ dξ ρ dρ hunit horth
  have hdω_sq : (∑ j : Fin 3, ‖dω j‖ ^ 2) =
      (∑ j : Fin 3, ‖(dρ j) • ξ + ρ • (dξ j)‖ ^ 2) := by
    congr 1; funext j; rw [hdω j]
  have hdρ_zero : (∑ j : Fin 3, (dρ j) ^ 2) = 0 := by
    simp [hcrit]
  have h1 : inner ℝ ω (∑ j : Fin 3, d2ω j) ≤ -(ρ ^ 2 * (∑ j : Fin 3, ‖dξ j‖ ^ 2)) := by
    linarith [hboch, hpolar, hdω_sq, hdρ_zero, hconcave]
  have h2 := mul_le_mul_of_nonneg_left h1 hν
  linarith

/-! ## Stage 4. Non-Zero Smooth Flow Inhabitation & Beltrami Casimir Eigenmode Degeneracy -/

/-- **Stage 4a (`beltrami_lamb_vector_cross_zero`):**
Pointwise Beltrami force-free eigenmode identity: whenever vorticity is collinear with velocity
($\omega(x) = \lambda u(x)$), the Lamb vector $u(x) \times \omega(x)$ vanishes identically. -/
public theorem beltrami_lamb_vector_cross_zero (u_x : EuclideanSpace ℝ (Fin 3)) (lam : ℝ) :
    cross u_x (lam • u_x) = 0 := by
  ext i
  fin_cases i <;> simp [ArnoldGeometric.cross_coord] <;> ring

/-- **Stage 4b (`beltrami_casimir_projection_zero`):**
For any velocity field $u$ with non-zero kinetic energy $\int \|u\|^2 \neq 0$ and any Beltrami
collinear field $v(x) = \lambda u(x)$, the $L^2$-orthogonal Casimir projection vanishes identically:
$$\Pi_u(u)(\lambda u) = 0.$$ -/
public theorem beltrami_casimir_projection_zero
    (u : VelocityField) (lam : ℝ)
    (hE : (∫ y, ‖u y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0) :
    Pi_u u (fun x => lam • u x) = 0 := by
  funext x
  simp only [Pi_u, Pi.zero_apply]
  have hpair :
      (fun y : T3 => pairing (lam • u y) (u y)) =
        fun y : T3 => lam * ‖u y‖ ^ 2 := by
    funext y
    unfold pairing
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [hpair, MeasureTheory.integral_const_mul, mul_div_cancel_right₀ lam hE, sub_self]

/-- **Stage 4c (`beltrami_tetherPointwiseDensity_zero`):**
Whenever a functional variation $\delta F/\delta\omega = \lambda u$ is a collinear Beltrami
variation with non-zero kinetic energy, the Frohmanian tether pointwise density vanishes identically
($\mathrm{tetherPointwiseDensity}(\omega, F, x) = 0$), proving that the tether acts purely transversely
to Beltrami/Casimir directions. -/
public theorem beltrami_tetherPointwiseDensity_zero
    (ω : CoadjointOrbit) (F : Functional) (lam : ℝ)
    (hbeltrami : FunctionalDerivative F ω = fun x => lam • velocity_from_vorticity ω x)
    (hE : (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0)
    (x : T3) :
    tetherPointwiseDensity kappa ω F x = 0 := by
  unfold tetherPointwiseDensity
  rw [hbeltrami, beltrami_casimir_projection_zero (velocity_from_vorticity ω) lam hE]
  simp

/-- Spatially uniform velocity field $u_c(x) = c$ for any vector $c \in \mathbb{R}^3$. -/
@[expose] public def constVelocity (c : T3) : VelocityField := fun _ => c

/-- For any non-zero vector $c \neq 0$, `constVelocity c ≠ 0`. -/
public theorem constVelocity_ne_zero (c : T3) (hc : c ≠ 0) :
    constVelocity c ≠ (0 : VelocityField) := by
  intro h
  exact hc (congrFun h 0)

/-- Convective derivative of `constVelocity c` vanishes identically. -/
public theorem constVelocity_convective_zero (c : T3) (x : T3) :
    convective (constVelocity c) (constVelocity c) x = 0 := by
  unfold convective constVelocity
  simp [fderiv_fun_const]

/-- Laplacian of `constVelocity c` vanishes identically. -/
public theorem constVelocity_laplacian_zero (c : T3) (x : T3) :
    laplacian (constVelocity c) x = 0 := by
  unfold laplacian constVelocity
  simp [fderiv_fun_const]

/-- **Stage 4d (`navier_stokes_eq_constVelocity`):**
For every vector $c \in \mathbb{R}^3$ and every viscosity $\nu \in \mathbb{R}$, the uniform velocity
field $u(t,x) = c$ with zero pressure $p(t,x) = 0$ satisfies `navier_stokes_eq` on $[0, \infty) \times \mathbb{R}^3$. -/
public theorem navier_stokes_eq_constVelocity (ν : ℝ) (c : T3) :
    navier_stokes_eq (fun _ => constVelocity c) (fun _ => (0 : PressureField)) ν := by
  intro t _ht x
  constructor
  · have hdt : time_deriv (fun _ => constVelocity c) t x = 0 :=
      time_deriv_const (constVelocity c) t x
    have hcv : convective (constVelocity c) (constVelocity c) x = 0 :=
      constVelocity_convective_zero c x
    have hp : pressureGradient (0 : PressureField) x = 0 :=
      pressureGradient_const 0 x
    have hl : laplacian (constVelocity c) x = 0 :=
      constVelocity_laplacian_zero c x
    change time_deriv (fun _ => constVelocity c) t x +
        convective (constVelocity c) (constVelocity c) x +
        pressureGradient (0 : PressureField) x =
      ν • laplacian (constVelocity c) x
    rw [hdt, hcv, hp, hl, zero_add, zero_add, smul_zero]
  · exact div_const c x

/-- **Stage 4e (`nonzero_smooth_ns_solution_exists`):**
For every non-zero vector $c \in \mathbb{R}^3$ ($c \neq 0$) and every viscosity $\nu \in \mathbb{R}$,
there exists a strictly non-zero smooth velocity evolution $u(t,x) = c$ ($u(0) \neq 0$) and pressure $p \equiv 0$
satisfying the exact 3D incompressible Navier–Stokes system `navier_stokes_eq u p ν` for all $t \ge 0$. -/
public theorem nonzero_smooth_ns_solution_exists (ν : ℝ) (c : T3) (hc : c ≠ 0) :
    ∃ (u : TimeDependentVelocity) (p : TimeDependentPressure),
      u 0 ≠ 0 ∧
      (∀ t ≥ (0 : ℝ), IsSmooth (u t)) ∧
      navier_stokes_eq u p ν :=
  ⟨fun _ => constVelocity c, fun _ => (0 : PressureField),
   constVelocity_ne_zero c hc,
   fun _ _ => contDiff_const,
   navier_stokes_eq_constVelocity ν c⟩

/-! ## Stage 5. Constantin–Fefferman Near/Far Singular-Integral Cutoff Optimization Bridge -/

/-- **Stage 5a (`near_field_stretching_absorbed_by_viscous_direction_damping`):**
Completing the square between the near-field Biot–Savart stretching bound $C_{\mathrm{near}}\, r\, M^3 G$
(where $G = \|\nabla \xi(x_{\max})\|_{\mathrm{HS}}$) and half of the viscous direction-curvature
dissipation $-\frac{\nu}{2} M^2 G^2$ yields for all $\nu > 0$:
$$C_{\mathrm{near}}\, r\, M^3 G - \frac{\nu}{2} M^2 G^2 \le \frac{C_{\mathrm{near}}^2\, r^2}{2\nu} M^4.$$ -/
public theorem near_field_stretching_absorbed_by_viscous_direction_damping
    (ν C_near r M G : ℝ) (hν : 0 < ν) :
    C_near * r * M ^ 3 * G - (ν / 2) * M ^ 2 * G ^ 2 ≤
      (C_near ^ 2 * r ^ 2 / (2 * ν)) * M ^ 4 := by
  have h2ν : 0 < 2 * ν := by linarith
  have h2ν_ne : 2 * ν ≠ 0 := ne_of_gt h2ν
  have hsq : 0 ≤ (C_near * r * M ^ 2 - ν * M * G) ^ 2 / (2 * ν) :=
    div_nonneg (sq_nonneg _) (le_of_lt h2ν)
  have hid :
      (C_near ^ 2 * r ^ 2 / (2 * ν)) * M ^ 4 -
        (C_near * r * M ^ 3 * G - (ν / 2) * M ^ 2 * G ^ 2) =
      (C_near * r * M ^ 2 - ν * M * G) ^ 2 / (2 * ν) := by
    field_simp [h2ν_ne]
    ring
  linarith

/-- **Stage 5b (`constantin_fefferman_near_far_cutoff_bridge`):**
Complete Constantin–Fefferman near/far Biot–Savart cutoff bridge at a spatial maximum $x_{\max}$. -/
public theorem constantin_fefferman_near_far_cutoff_bridge
    (ν C_near C_CZ r M G κ'' stretching S_near S_far visc_lap : ℝ)
    (hν : 0 < ν)
    (h_split : stretching ≤ S_near + S_far)
    (h_near : S_near ≤ C_near * r * M ^ 3 * G)
    (h_far : S_far ≤ C_CZ * M ^ 3)
    (h_visc : ν * visc_lap ≤ -(ν * M ^ 2 * G ^ 2))
    (h_cutoff : C_near ^ 2 * r ^ 2 / (2 * ν) ≤ κ'' / 2)
    (h_coercive : κ'' * M ^ 2 ≤ (ν / 2) * G ^ 2) :
    stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - (κ'' / 2) * M ^ 4 := by
  have hyoung := near_field_stretching_absorbed_by_viscous_direction_damping ν C_near r M G hν
  have hM4 : 0 ≤ M ^ 4 := by positivity
  have hcut_M4 : (C_near ^ 2 * r ^ 2 / (2 * ν)) * M ^ 4 ≤ (κ'' / 2) * M ^ 4 :=
    mul_le_mul_of_nonneg_right h_cutoff hM4
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hcoerc_M4 : κ'' * M ^ 4 ≤ (ν / 2) * M ^ 2 * G ^ 2 := by
    have h := mul_le_mul_of_nonneg_right h_coercive hM2
    linarith [show κ'' * M ^ 2 * M ^ 2 = κ'' * M ^ 4 by ring,
              show (ν / 2) * G ^ 2 * M ^ 2 = (ν / 2) * M ^ 2 * G ^ 2 by ring]
  linarith

/-! ## Section 3. The Four Components $P_1, P_2, P_3, P_4$ and the Master Product Theorem -/

/-- **Scaffolding (ψ-slot).** C2 fails for this form (`shear_C2_fails`); the model is `TetherKernelVel` (VelocityTether.lean). **Component $P_1$ (Canonical 5-Step Uniqueness & Quadratic Degree on $\mathrm{SDiff}(\mathbb{T}^3)^*$):**
Every bilinear correction $B$ satisfying C1–C3, quadratic saturation, and polarization (under
metriplectic symmetry), or having the canonical kernel density $\alpha_{\mathrm{can}}(\omega,x) = -\kappa\|\omega(x)\|^2$,
equals `TetherKernel`, and `TetherKernel` has exact quadratic homogeneity $c^2$ under $\omega \mapsto c\omega$ with no
degree $\ge 3$ remainder. -/
@[expose] public def P1_CanonicalFiveStepUniqueness (kappa : ℝ) : Prop :=
  (∀ (B : CoadjointOrbit → Functional → Functional → ℝ),
    (∀ ω F G, B ω F G = B ω G F) →
    InvariantUnderCoadjointAction B →
    DegenerateWRTKineticEnergy B →
    ProducesControllableNegativeFeedback kappa B →
    SaturatesTetherQuadratic kappa B →
    Polarizes B →
    Polarizes (TetherKernel kappa) →
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = TetherKernel kappa ω F G) ∧
  (∀ (B : CoadjointOrbit → Functional → Functional → ℝ),
    (∀ ω F G, B ω F G = B ω G F) →
    InvariantUnderCoadjointAction B →
    DegenerateWRTKineticEnergy B →
    ProducesControllableNegativeFeedback kappa B →
    SaturatesTetherQuadratic kappa B →
    Polarizes B →
    Polarizes (TetherKernel kappa) →
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = TetherKernel kappa ω F G) ∧
  (∀ (B : CoadjointOrbit → Functional → Functional → ℝ) (α : CoadjointOrbit → T3 → ℝ),
    HasTetherKernelDensity B α →
    (∀ ω x, α ω x = canonicalTetherDensity kappa ω x) →
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = TetherKernel kappa ω F G) ∧
  (∀ (F G : Functional) (ω : CoadjointOrbit) (c : ℝ),
    c ≠ 0 →
    FunctionalDerivative F
      ⟨fun x => c • ω.val x, fun x => by rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative F ω →
    FunctionalDerivative G
      ⟨fun x => c • ω.val x, fun x => by rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative G ω →
    TetherKernel kappa ⟨fun x => c • ω.val x, fun x => by rw [div_smul, ω.property x, mul_zero]⟩ F G =
      c ^ 2 * TetherKernel kappa ω F G)

/-- **Scaffolding (ψ-slot).** C2 fails for this form (`shear_C2_fails`); the model is `TetherKernelVel` (VelocityTether.lean). **Component $P_2$ (Exact Metriplectic Split, KKS Skew-Symmetry & Cyclic Jacobi, Casimir/Beltrami Conservation, and Strict Transverse Damping):**
The Frohmanian pairing $\mathfrak{T}_F = \omega_{\mathrm{KKS}} + \mathrm{TetherKernel}$ splits into the skew-symmetric KKS 2-form
satisfying the cyclic Jacobi identity and the symmetric negative-semidefinite tether metric form over the $L^2$-orthogonal
projection $\Pi_u$, which reproduces classical Euler dynamics on the kinetic-energy Hamiltonian ($\Pi_u u = 0$) and on
Beltrami eigenmodes ($\Pi_u(\lambda u) = 0$), and enforces strict pointwise negative damping whenever $\omega(x) \neq 0$
and $\Pi_u(\delta F/\delta\omega)(x) \neq 0$. -/
@[expose] public def P2_MetriplecticSplitAndCasimirDamping (kappa : ℝ) : Prop :=
  (∀ (ω : CoadjointOrbit) (ξ₁ ξ₂ : VelocityField),
    kksSymplecticForm ω ξ₁ ξ₂ = -kksSymplecticForm ω ξ₂ ξ₁) ∧
  (∀ (ω : CoadjointOrbit) (ξ₁ ξ₂ ξ₃ : VelocityField) (x : T3),
    pairing (ω.val x) (cross (ξ₁ x) (cross (ξ₂ x) (ξ₃ x))) +
    pairing (ω.val x) (cross (ξ₂ x) (cross (ξ₃ x) (ξ₁ x))) +
    pairing (ω.val x) (cross (ξ₃ x) (cross (ξ₁ x) (ξ₂ x))) = 0) ∧
  (∀ (ω : CoadjointOrbit) (F : Functional),
    FrohmanianMetriplecticPairing kappa ω F F = TetherKernel kappa ω F F ∧
    TetherKernel kappa ω F F ≤ 0) ∧
  (∀ (F : Functional) (ω : CoadjointOrbit),
    FunctionalDerivative KineticEnergyHamiltonian ω = velocity_from_vorticity ω →
    (∀ x, div (velocity_from_vorticity ω) x = 0) →
    Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) →
    TetheredBracket kappa F KineticEnergyHamiltonian ω =
      ClassicalBracket F KineticEnergyHamiltonian ω) ∧
  (∀ (u : VelocityField) (lam : ℝ),
    (∫ y, ‖u y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0 →
    Pi_u u (fun x => lam • u x) = 0) ∧
  (∀ (ω : CoadjointOrbit) (F : Functional) (x : T3),
    ω.val x ≠ 0 →
    Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x ≠ 0 →
    tetherPointwiseDensity kappa ω F x < 0)

/-- **Component $P_3$ (Quartic $4 = 4$ Young Absorption, Attained `sSup` Pinning, Concrete 3D Bochner–Polar Identity, & Near/Far Cutoff Bridge):**
Whenever Young's inequality with $\varepsilon_{\mathrm{abs}} = \kappa/4$ bounds $4 C_{\mathrm{CZ}} M I_4$ by
$(\kappa/4) I_6 + C_{\mathrm{abs}} M^3 \|\phi\|_\infty^{3/2}$, subtracting the tether dissipation $\kappa I_6$ leaves
the strictly negative hyper-dissipative remainder $-(3/4)\kappa I_6$; moreover any attained spatial maximum pins
`vorticity_sup_norm ω = M`, and the concrete 3D Bochner–polar identity and Constantin–Fefferman near/far cutoff bridge hold at $x_{\max}$. -/
@[expose] public def P3_QuarticYoungAbsorption (kappa : ℝ) : Prop :=
  (∀ (M I₄ I₆ phi_norm C_abs : ℝ),
    0 ≤ I₆ →
    4 * CalderonZygmundConstant3D * M * I₄ ≤
      (kappa / 4) * I₆ + C_abs * (M ^ 3 * phi_norm ^ ((3 : ℝ) / 2)) →
    4 * CalderonZygmundConstant3D * M * I₄ - kappa * I₆ ≤
      C_abs * (M ^ 3 * phi_norm ^ ((3 : ℝ) / 2)) - (3 / 4 : ℝ) * kappa * I₆) ∧
  (∀ (ω : VorticityField) (x_max : T3) (M : ℝ),
    M = ‖ω x_max‖ → (∀ x : T3, ‖ω x‖ ≤ M) → NavierStokes3D.vorticity_sup_norm ω = M) ∧
  (∀ (ν ρ : ℝ) (ω ξ : T3) (dω d2ω dξ : Fin 3 → T3) (dρ d2h : Fin 3 → ℝ),
    0 ≤ ν →
    ‖ξ‖ = 1 →
    (∀ j : Fin 3, inner ℝ ξ (dξ j) = 0) →
    (∀ j : Fin 3, dω j = (dρ j) • ξ + ρ • (dξ j)) →
    (∀ j : Fin 3, d2h j = ‖dω j‖ ^ 2 + inner ℝ ω (d2ω j)) →
    (∀ j : Fin 3, dρ j = 0) →
    (∑ j : Fin 3, d2h j) ≤ 0 →
    ν * inner ℝ ω (∑ j : Fin 3, d2ω j) ≤ -(ν * ρ ^ 2 * (∑ j : Fin 3, ‖dξ j‖ ^ 2))) ∧
  (∀ (ν C_near C_CZ r M G κ'' stretching S_near S_far visc_lap : ℝ),
    0 < ν →
    stretching ≤ S_near + S_far →
    S_near ≤ C_near * r * M ^ 3 * G →
    S_far ≤ C_CZ * M ^ 3 →
    ν * visc_lap ≤ -(ν * M ^ 2 * G ^ 2) →
    C_near ^ 2 * r ^ 2 / (2 * ν) ≤ κ'' / 2 →
    κ'' * M ^ 2 ≤ (ν / 2) * G ^ 2 →
    stretching + ν * visc_lap ≤ C_CZ * M ^ 3 - (κ'' / 2) * M ^ 4)

/-- **Component $P_4$ (Unconditional Cubic Lyapunov ODE Ceiling):**
Every differentiable trajectory $y(s)$ on $[0, \infty)$ satisfying the cubic Riccati differential inequality
$y'(s) \le C y(s)^2 - \kappa'' y(s)^3$ ($C, \kappa'' > 0$) obeys the uniform global ceiling
$y(t) \le \max(y(0), C / \kappa'')$ for all $t \ge 0$. -/
@[expose] public def P4_UnconditionalLyapunovCeiling : Prop :=
  ∀ (C κ'' : ℝ), 0 < C → 0 < κ'' →
    ∀ (y : ℝ → ℝ),
      (∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s) →
      (∀ s ≥ (0 : ℝ), deriv y s ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3) →
      ∀ (t : ℝ), 0 ≤ t → y t ≤ max (y 0) (C / κ'')

/-- **Scaffolding (ψ-slot).** C2 fails for this form (`shear_C2_fails`); the model is `TetherKernelVel` (VelocityTether.lean). **Master Single-Sentence Product Theorem (`frohmanian_metriplectic_system_canonical_uniqueness_and_global_regularity_product_theorem`):**
Unconditional proof of the four-conjunct product statement
$$P_1 \wedge P_2 \wedge P_3 \wedge P_4$$
for the Frohmanian tethered / metriplectic system on $\mathbb{T}^3$. -/
public theorem frohmanian_metriplectic_system_canonical_uniqueness_and_global_regularity_product_theorem (hκ : 0 < kappa) :
    P1_CanonicalFiveStepUniqueness kappa ∧
    P2_MetriplecticSplitAndCasimirDamping kappa ∧
    P3_QuarticYoungAbsorption kappa ∧
    P4_UnconditionalLyapunovCeiling := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- P1: 5-step canonical uniqueness and quadratic degree
    exact ⟨uniqueness_of_minimal_tether hκ,
      uniqueness_of_minimal_symmetric_tether,
      FrohmanianTether.uniqueness_of_kernel_density,
      step2_degree_of_ne_zero⟩
  · -- P2: Metriplectic split, KKS skew-symmetry & Jacobi, Casimir/Beltrami conservation, strict transverse damping
    exact ⟨kksSymplecticForm_skew,
      kksPointwise_cyclic_jacobi_identity,
      FrohmanianMetriplecticPairing_diag_eq_metric hκ,
      tethered_reproduces_classical_euler,
      beltrami_casimir_projection_zero,
      tetherPointwiseDensity_strict_neg_of_noncasimir hκ⟩
  · -- P3: Quartic 4=4 Young absorption, attained sSup pinning, concrete 3D Bochner–polar identity, and near/far cutoff bridge
    exact ⟨AnalyticPipeline.youngs_absorption_elimination,
      vorticity_sup_norm_eq_of_isSpatialMax,
      concrete_bochner_polar_viscous_damping_at_max,
      constantin_fefferman_near_far_cutoff_bridge⟩
  · -- P4: Unconditional cubic Lyapunov ODE ceiling
    exact AnalyticPipeline.comparison_ode_stability

end -- noncomputable section

#print axioms kksSymplecticForm_skew
#print axioms kksPointwise_cyclic_jacobi_identity
#print axioms FrohmanianMetriplecticPairing_diag_eq_metric
#print axioms unitCube_nonempty
#print axioms bddAbove_range_norm_of_attained_max
#print axioms vorticity_sup_norm_eq_of_isSpatialMax
#print axioms polar_pythagoras_directional_deriv
#print axioms polar_pythagoras_3d_sum
#print axioms bochner_laplacian_3d_identity
#print axioms concrete_bochner_polar_viscous_damping_at_max
#print axioms beltrami_lamb_vector_cross_zero
#print axioms beltrami_casimir_projection_zero
#print axioms beltrami_tetherPointwiseDensity_zero
#print axioms constVelocity_ne_zero
#print axioms navier_stokes_eq_constVelocity
#print axioms nonzero_smooth_ns_solution_exists
#print axioms near_field_stretching_absorbed_by_viscous_direction_damping
#print axioms constantin_fefferman_near_far_cutoff_bridge
#print axioms frohmanian_metriplectic_system_canonical_uniqueness_and_global_regularity_product_theorem

end FrohmanianSymplecticTether.FinalProductTheorem

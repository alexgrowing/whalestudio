import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ThetaAH

variable {g : ℕ}

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
private lemma intCast_dotProduct' (k m : Fin g → ℤ) :
    ((k ⬝ᵥ m : ℤ) : ℂ) = (fun i => (k i : ℂ)) ⬝ᵥ (fun i => (m i : ℂ)) := by
  simp [dotProduct]

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in

theorem _root_.GlobalTheory.ThetaAH.thetaChar_add_period {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm) (a b w : Fin g → ℂ)
    (m n : Fin g → ℤ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b (w + ((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)))) =
      Complex.exp (Real.pi * Complex.I * (2 * (a ⬝ᵥ fun i => (m i : ℂ)) - 2 * ((fun i => (n i : ℂ)) ⬝ᵥ b)
        - ((fun i => (n i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (n i : ℂ)) - 2 * ((fun i => (n i : ℂ)) ⬝ᵥ w))) *
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ a b w := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar
  rw [← (Equiv.subRight n).tsum_eq, ← tsum_mul_left]
  congr 1
  funext k
  set N : Fin g → ℂ := fun i => (n i : ℂ)
  set M : Fin g → ℂ := fun i => (m i : ℂ)
  set K : Fin g → ℂ := fun i => (k i : ℂ)
  have hc : (fun i => (((Equiv.subRight n k) i : ℤ) : ℂ)) = K - N := by
    funext i; simp [K, N]
  have hsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ τ *ᵥ y = y ⬝ᵥ τ *ᵥ x := by
    intro x y
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hs.eq]
  rw [hc, ← Complex.exp_add]
  have key : Real.pi * Complex.I * ((K - N + a) ⬝ᵥ τ *ᵥ (K - N + a)) +
      2 * Real.pi * Complex.I * ((K - N + a) ⬝ᵥ (w + (M + τ *ᵥ N) + b)) =
      Real.pi * Complex.I * (2 * (a ⬝ᵥ M) - 2 * (N ⬝ᵥ b) - (N ⬝ᵥ τ *ᵥ N) - 2 * (N ⬝ᵥ w)) +
      (Real.pi * Complex.I * ((K + a) ⬝ᵥ τ *ᵥ (K + a)) +
        2 * Real.pi * Complex.I * ((K + a) ⬝ᵥ (w + b))) +
      (((k ⬝ᵥ m - n ⬝ᵥ m : ℤ) : ℂ)) * (2 * Real.pi * Complex.I) := by
    have h1 := hsym N (K + a)
    push_cast
    rw [intCast_dotProduct', intCast_dotProduct']
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, dotProduct_sub, sub_dotProduct, dotProduct_add,
      add_dotProduct] at h1 ⊢
    linear_combination (-(Real.pi * Complex.I)) * h1
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
theorem _root_.GlobalTheory.ThetaAH.hermForm_pullback (h B : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (hᵀ * B * h.map (starRingEnd ℂ)) z w = (h *ᵥ z) ⬝ᵥ B *ᵥ star (h *ᵥ w) := by
  have hs : h.map (starRingEnd ℂ) *ᵥ star w = star (h *ᵥ w) := by
    funext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
private lemma inv_im_transpose_eq_and_mul_eq_one (τ : Matrix (Fin g) (Fin g) ℂ) (hY : (τ.map Complex.im).PosDef) :
    (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)))ᵀ =
      ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) ∧
    ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *
      (τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) = 1 := by
  have hdet : IsUnit (τ.map Complex.im).det := isUnit_iff_ne_zero.mpr hY.det_pos.ne'
  constructor
  · rw [← Matrix.transpose_map]
    congr 1
    have := hY.isHermitian.inv
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  · have := Matrix.nonsing_inv_mul _ hdet
    have h2 := congrArg (fun A => A.map (Complex.ofRealHom)) this
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
private lemma re_quadratic_sub_hermitian_eq_im_form (S : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℂ) :
    (Real.pi / 2 * (v ⬝ᵥ (S.map (fun x : ℝ => (x : ℂ)) *ᵥ v))).re +
      (Real.pi / 2 * (v ⬝ᵥ (S.map (fun x : ℝ => (x : ℂ)) *ᵥ v))).re
      + -Real.pi * (v ⬝ᵥ S.map (fun x : ℝ => (x : ℂ)) *ᵥ star v).re =
      -2 * Real.pi * ((fun i => (v i).im) ⬝ᵥ (S *ᵥ fun i => (v i).im)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Complex.re_sum]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Complex.mul_im]
  ring

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in
private lemma star_lattice_vector_eq (τ : Matrix (Fin g) (Fin g) ℂ) (m n : Fin g → ℤ) :
    star ((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) =
      ((fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) -
        (2 * Complex.I) • ((τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) *ᵥ (fun i => (n i : ℂ))) := by
  funext i
  apply Complex.ext <;> simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum] <;> ring

open NumberField in
open AlgebraicGeometry CategoryTheory Limits in
open scoped Matrix nonZeroDivisors in
variable {g : ℕ} in

theorem _root_.GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy : ∀ (g : ℕ) (τ h Hm : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (q : (Fin g → ℂ) → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) → (∀ z, q z = Real.pi / 2 * ((h *ᵥ z) ⬝ᵥ (((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ (h *ᵥ z)))) → (∀ z, ‖Complex.exp (q z)‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) = Real.exp (-2 * Real.pi * ((fun i => ((h *ᵥ z) i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ fun i => ((h *ᵥ z) i).im)))) ∧ ∀ (lam : Fin g → ℂ) (m n : Fin g → ℤ), h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) → ∃ χ : ℂ, ‖χ‖ = 1 ∧ ∀ z, Complex.exp (q (z + lam)) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ (h *ᵥ (z + lam)) = χ * Complex.exp (Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z lam + Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm lam lam) * (Complex.exp (q z) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ (h *ᵥ z)) := by
  intro g τ h Hm c₁ c₂ q hs hY hc₁ hc₂ hHm hq
  obtain ⟨hST, hSY⟩ := inv_im_transpose_eq_and_mul_eq_one τ hY
  set S : Matrix (Fin g) (Fin g) ℂ := ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) with hSdef
  have hSsym : ∀ x y : Fin g → ℂ, x ⬝ᵥ S *ᵥ y = y ⬝ᵥ S *ᵥ x := by
    intro x y
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hST]
  refine ⟨fun z => ?_, fun lam m n hlam => ?_⟩
  · rw [hq, hHm, _root_.GlobalTheory.ThetaAH.hermForm_pullback, Complex.norm_exp, sq, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    exact re_quadratic_sub_hermitian_eq_im_form _ (h *ᵥ z)
  set N : Fin g → ℂ := fun i => (n i : ℂ) with hN
  set M : Fin g → ℂ := fun i => (m i : ℂ) with hM
  have him : ∀ c : Fin g → ℂ, (∀ i, c i = 0 ∨ c i = 1 / 2) → (c ⬝ᵥ M).im = 0 ∧ (N ⬝ᵥ c).im = 0 := by
    intro c hc
    constructor
    · simp only [dotProduct, Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hc i with h0 | h0 <;> simp [h0, M]
    · simp only [dotProduct, Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rcases hc i with h0 | h0 <;> simp [h0, N]
  refine ⟨Complex.exp (Real.pi * Complex.I * (M ⬝ᵥ N + 2 * (c₁ ⬝ᵥ M) - 2 * (N ⬝ᵥ c₂))), ?_,
    fun z => ?_⟩
  · have hMN : (M ⬝ᵥ N).im = 0 := by
      simp [dotProduct, Complex.im_sum, M, N]
    rw [Complex.norm_exp, Real.exp_eq_one_iff]
    simp [Complex.mul_re, hMN, (him c₁ hc₁).1, (him c₂ hc₂).2]
  obtain ⟨v, hv⟩ : ∃ v, h *ᵥ z = v := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, h *ᵥ lam = μ := ⟨_, rfl⟩
  rw [hμ] at hlam
  have hstar : star μ = μ - (2 * Complex.I) • ((τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) *ᵥ N) := by
    rw [hlam]; exact star_lattice_vector_eq τ m n
  have hSYN : S *ᵥ ((τ.map Complex.im).map (fun x : ℝ => (x : ℂ)) *ᵥ N) = N := by
    rw [Matrix.mulVec_mulVec, hSY, Matrix.one_mulVec]
  have hSstar : S *ᵥ star μ = S *ᵥ μ - (2 * Complex.I) • N := by
    rw [hstar, Matrix.mulVec_sub, Matrix.mulVec_smul, hSYN]
  have f1 : v ⬝ᵥ S *ᵥ star μ = v ⬝ᵥ S *ᵥ μ - 2 * Complex.I * (v ⬝ᵥ N) := by
    rw [hSstar, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have f2 : μ ⬝ᵥ S *ᵥ star μ = μ ⬝ᵥ S *ᵥ μ - 2 * Complex.I * (μ ⬝ᵥ N) := by
    rw [hSstar, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have f3 : μ ⬝ᵥ N = M ⬝ᵥ N + N ⬝ᵥ τ *ᵥ N := by
    rw [hlam, add_dotProduct, dotProduct_comm (τ *ᵥ N)]
  have f4 : (v + μ) ⬝ᵥ S *ᵥ (v + μ) = v ⬝ᵥ S *ᵥ v + 2 * (v ⬝ᵥ S *ᵥ μ) + μ ⬝ᵥ S *ᵥ μ := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hSsym μ v]
    ring
  have f5 : N ⬝ᵥ v = v ⬝ᵥ N := dotProduct_comm _ _
  have htheta : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ (h *ᵥ (z + lam)) =
      Complex.exp (Real.pi * Complex.I * (2 * (c₁ ⬝ᵥ M) - 2 * (N ⬝ᵥ c₂) - (N ⬝ᵥ τ *ᵥ N)
        - 2 * (N ⬝ᵥ v))) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar τ c₁ c₂ v := by
    rw [Matrix.mulVec_add, hv, hμ, hlam]
    exact _root_.GlobalTheory.ThetaAH.thetaChar_add_period hs c₁ c₂ v m n
  rw [htheta, hq (z + lam), hq z, hHm, _root_.GlobalTheory.ThetaAH.hermForm_pullback,
    _root_.GlobalTheory.ThetaAH.hermForm_pullback, Matrix.mulVec_add, hv, hμ,
    ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
  congr 2
  linear_combination (Real.pi / 2) * f4 - Real.pi * f1 - (Real.pi / 2) * f2 +
    (Real.pi * Complex.I) * f3 - (2 * Real.pi * Complex.I) * f5

end GlobalTheory.ThetaAH

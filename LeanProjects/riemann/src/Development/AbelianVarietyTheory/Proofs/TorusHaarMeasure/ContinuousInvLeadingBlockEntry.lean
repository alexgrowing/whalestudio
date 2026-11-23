import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SharpGradient

open Filter Matrix
open scoped ComplexOrder ComplexConjugate

section Calculus

variable {n : ℕ}

def SharpAt (φ : V n → ℝ) (x : V n) (ξ : Fin n → ℂ) : Prop :=
  ContDiffAt ℝ 2 φ x ∧ 0 ≤ φ x ∧ 0 ≤ (leviV n (fun y => (φ y : ℂ)) x ξ).re ∧
    Complex.normSq (∑ j, wd n j (fun y => (φ y : ℂ)) x * ξ j) ≤
      φ x * (leviV n (fun y => (φ y : ℂ)) x ξ).re

theorem SharpAt.of_minorant {φ ψ : V n → ℝ} {x : V n} {ξ : Fin n → ℂ} (h : SharpAt ψ x ξ)
    (hφ : ContDiffAt ℝ 2 φ x) (hle : ∀ᶠ v in 𝓝 x, ψ v ≤ φ v) (heq : φ x = ψ x) :
    SharpAt φ x ξ := by
  obtain ⟨hψ, h0, hL, hb⟩ := h
  have hrd : DifferentiableAt ℝ φ x := hφ.differentiableAt (by simp)
  have hψd : DifferentiableAt ℝ ψ x := hψ.differentiableAt (by simp)
  have hmin : IsLocalMin (fun y => φ y - ψ y) x := by
    filter_upwards [hle] with v hv
    linarith
  have hfd : fderiv ℝ φ x = fderiv ℝ ψ x := by
    have h := hmin.fderiv_eq_zero
    rw [fderiv_fun_sub hrd hψd] at h
    exact sub_eq_zero.1 h
  have hwd : ∀ j, wd n j (fun y => (φ y : ℂ)) x = wd n j (fun y => (ψ y : ℂ)) x := by
    intro j
    simp only [wd, fderiv_ofReal_apply hrd, fderiv_ofReal_apply hψd, hfd]
  have hmax : IsLocalMax (fun y => ψ y + (-1) * φ y) x := by
    have := hmin.neg
    refine this.congr ?_
    filter_upwards with y
    ring
  have hcd : ContDiffAt ℝ 2 (fun y => ψ y + (-1) * φ y) x := hψ.add (contDiffAt_const.mul hφ)
  have h2 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hcd hmax ξ
  rw [ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add hψ (contDiffAt_const.mul hφ) ξ,
    ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hφ ξ] at h2
  have h3 : (leviV n (fun y => (ψ y : ℂ)) x ξ).re ≤ (leviV n (fun y => (φ y : ℂ)) x ξ).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at h2
    linarith
  refine ⟨hφ, heq ▸ h0, hL.trans h3, ?_⟩
  simp only [hwd]
  rw [heq]
  exact hb.trans (mul_le_mul_of_nonneg_left h3 h0)

theorem normSq_sum_le {ι : Type} [Fintype ι] (a : ι → ℂ) (s L : ι → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hL : ∀ i, 0 ≤ L i) (h : ∀ i, Complex.normSq (a i) ≤ s i * L i) :
    Complex.normSq (∑ i, a i) ≤ (∑ i, s i) * ∑ i, L i := by
  rw [Complex.normSq_eq_norm_sq]
  have h1 : ‖∑ i, a i‖ ≤ ∑ i, ‖a i‖ := norm_sum_le _ _
  have h2 := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
    (r := fun i => ‖a i‖) (f := s) (g := L) (fun i _ => hs i) (fun i _ => hL i)
    (fun i _ => by rw [← Complex.normSq_eq_norm_sq]; exact h i)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem sharpAt_sum {m : ℕ} {u : Fin m → V n → ℝ} {x : V n} {ξ : Fin n → ℂ}
    (h : ∀ i, SharpAt (u i) x ξ) : SharpAt (fun y => ∑ i, u i y) x ξ := by
  have hc : ∀ i, ContDiffAt ℝ 2 (u i) x := fun i => (h i).1
  have hL := H.leviV_ofReal_sum hc ξ
  have hw : ∑ j, wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x * ξ j =
      ∑ i, ∑ j, wd n j (fun y => (u i y : ℂ)) x * ξ j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H.wd_ofReal_sum (fun i => (hc i).differentiableAt (by simp)), Finset.sum_mul]
  refine ⟨ContDiffAt.sum fun i _ => hc i, Finset.sum_nonneg fun i _ => (h i).2.1, ?_, ?_⟩
  · rw [hL, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => (h i).2.2.1
  · rw [hL, hw, Complex.re_sum]
    exact normSq_sum_le _ _ _ (fun i => (h i).2.1) (fun i => (h i).2.2.1) fun i => (h i).2.2.2

theorem sharpAt_sum' {ι : Type} [Fintype ι] {u : ι → V n → ℝ} {x : V n} {ξ : Fin n → ℂ}
    (h : ∀ i, SharpAt (u i) x ξ) : SharpAt (fun y => ∑ i, u i y) x ξ := by
  have e : (fun y => ∑ i, u i y) = fun y => ∑ k, u ((Fintype.equivFin ι).symm k) y := by
    funext y
    exact ((Fintype.equivFin ι).symm.sum_comp (fun i => u i y)).symm
  rw [e]
  exact sharpAt_sum fun k => h _

theorem sharpAt_ball {m : ℕ} {g : Fin m → V n → ℂ} {x : V n} (ξ : Fin n → ℂ)
    (hg : ∀ i, ContDiffAt ℂ 2 (g i) x) (hlt : ∑ i, Complex.normSq (g i x) < 1) :
    SharpAt (fun y => -Real.log (1 - ∑ i, Complex.normSq (g i y))) x ξ := by
  set k : ℝ → ℝ := fun t => -Real.log (1 - t) with hk
  have hu : ∀ i, ContDiffAt ℝ 2 (fun y => Complex.normSq (g i y)) x := fun i =>
    H.contDiffAt_normSq_comp (hg i)
  have hS : ContDiffAt ℝ 2 (fun y => ∑ i, Complex.normSq (g i y)) x :=
    ContDiffAt.sum fun i _ => hu i
  set t := ∑ i, Complex.normSq (g i x) with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h1t : 0 < 1 - t := by linarith
  have hkc : ContDiffAt ℝ 2 k t := by
    refine ContDiffAt.neg ?_
    exact (Real.contDiffAt_log.2 h1t.ne').comp t (contDiffAt_const.sub contDiffAt_id)
  have hd1 : deriv k = fun s => (1 - s)⁻¹ := by
    funext s
    simp only [hk]
    rw [deriv.fun_neg, deriv_comp_const_sub Real.log, Real.deriv_log, neg_neg]
  have hd2 : deriv (deriv k) t = ((1 - t) ^ 2)⁻¹ := by
    rw [hd1, deriv_comp_const_sub (fun s : ℝ => s⁻¹), deriv_inv, neg_neg]
  have hc := H.leviChain n k (fun y => ∑ i, Complex.normSq (g i y)) x ξ hS hkc
  set η : Fin m → ℂ := fun i => ∑ j, wd n j (g i) x * ξ j with hη
  have hw : ∑ j, wd n j (fun y => ((∑ i, Complex.normSq (g i y) : ℝ) : ℂ)) x * ξ j =
      ∑ i, η i * conj (g i x) := by
    simp only [hη, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [H.wd_ofReal_sum (u := fun i y => Complex.normSq (g i y))
      (fun i => (hu i).differentiableAt (by simp)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [H.wd_normSq_comp (hg i)]; ring
  rw [H.leviV_ofReal_sum (u := fun i y => Complex.normSq (g i y)) hu, hw, ← ht, hd2, hd1] at hc
  simp only [fun i => H.leviV_normSq_comp (hg i) ξ] at hc
  set N := Complex.normSq (∑ i, η i * conj (g i x)) with hN
  set M := ∑ i, Complex.normSq (η i) with hM
  have hN0 : 0 ≤ N := Complex.normSq_nonneg _
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hNM : N ≤ M * t := by
    refine normSq_sum_le _ _ _ (fun i => Complex.normSq_nonneg _)
      (fun i => Complex.normSq_nonneg _) fun i => ?_
    rw [Complex.normSq_mul, Complex.normSq_conj]
  have hL : (leviV n (fun y => ((-Real.log (1 - ∑ i, Complex.normSq (g i y)) : ℝ) : ℂ)) x ξ).re =
      (1 - t)⁻¹ * M + ((1 - t) ^ 2)⁻¹ * N := by
    have : leviV n (fun y => ((-Real.log (1 - ∑ i, Complex.normSq (g i y)) : ℝ) : ℂ)) x ξ =
        (((1 - t)⁻¹ * M + ((1 - t) ^ 2)⁻¹ * N : ℝ) : ℂ) := by
      refine hc.trans ?_
      simp only [hM, hη, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sum]
    rw [this, Complex.ofReal_re]
  have hG : ∑ j, wd n j (fun y => ((-Real.log (1 - ∑ i, Complex.normSq (g i y)) : ℝ) : ℂ)) x * ξ j
      = (((1 - t)⁻¹ : ℝ) : ℂ) * ∑ i, η i * conj (g i x) := by
    rw [← hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := wd_ofReal_comp (j := j) (k := k) (v := fun y => ∑ i, Complex.normSq (g i y)) (x := x)
      (hkc.differentiableAt (by simp)) (hS.differentiableAt (by simp))
    rw [hd1] at this
    rw [← mul_assoc, ← this]
  have hlog : t ≤ -Real.log (1 - t) := by
    have := Real.log_le_sub_one_of_pos h1t
    linarith
  have hi : 0 < (1 - t)⁻¹ := inv_pos.2 h1t
  have hL0 : 0 ≤ (1 - t)⁻¹ * M + ((1 - t) ^ 2)⁻¹ * N := by positivity
  have hcc : ContDiffAt ℝ 2 (k ∘ fun y => ∑ i, Complex.normSq (g i y)) x := hkc.comp x hS
  refine ⟨hcc, ht0.trans hlog, hL ▸ hL0, ?_⟩
  rw [hL, hG, Complex.normSq_mul, Complex.normSq_ofReal, ← hN]
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hlog hL0)
  have e : t * ((1 - t)⁻¹ * M + ((1 - t) ^ 2)⁻¹ * N) - (1 - t)⁻¹ * (1 - t)⁻¹ * N =
      (1 - t)⁻¹ * (M * t - N) := by
    field_simp
    ring
  have : 0 ≤ (1 - t)⁻¹ * (M * t - N) := mul_nonneg hi.le (by linarith)
  linarith

end Calculus

section Matrices

theorem det_le_prod_diag {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A.PosDef) :
    A.det.re ≤ ∏ i, (A i i).re := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hd : ∀ i, 0 < A i i := fun i => hA.diag_pos
  have hre : ∀ i, ((A i i).re : ℂ) = A i i := fun i =>
    Complex.ext (by simp) (by simp [(Complex.lt_def.1 (hd i)).2.symm])
  have hD : (Matrix.diagonal fun i => A i i).PosDef := Matrix.posDef_diagonal_iff.2 hd
  have h := RgB.amgm hm hA hD
  have hinv : (Matrix.diagonal fun i => A i i)⁻¹ = Matrix.diagonal fun i => (A i i)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd i).ne'
  have htr : (A * (Matrix.diagonal fun i => A i i)⁻¹).trace.re = m := by
    rw [hinv]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal, mul_inv_cancel₀ (hd _).ne']
    simp
  have hdet : (Matrix.diagonal fun i => A i i).det.re = ∏ i, (A i i).re := by
    rw [Matrix.det_diagonal, ← Complex.ofReal_re (∏ i, (A i i).re), Complex.ofReal_prod]
    simp only [hre]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [htr, hdet, div_self hmR.ne', mul_one] at h
  have hp : 0 ≤ ∏ i, (A i i).re := Finset.prod_nonneg fun i _ => (Complex.lt_def.1 (hd i)).1.le
  exact (Real.rpow_le_rpow_iff (ExhA.det_re_pos_im hA).1.le hp (inv_pos.2 hmR)).1 h

theorem conj_diag {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : Uᴴ * U = 1)
    (Z : Matrix (Fin p) (Fin q) ℂ) (a : Fin p) :
    ((Uᴴ * (1 - Z * Zᴴ) * U : Matrix (Fin p) (Fin p) ℂ) a a).re = 1 - ∑ b, Complex.normSq ((Uᴴ * Z) a b) := by
  have e : Uᴴ * (1 - Z * Zᴴ) * U = 1 - (Uᴴ * Z) * (Uᴴ * Z)ᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, hU]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.sub_apply, Matrix.mul_apply]
  simp only [Matrix.one_apply_eq, Complex.sub_re, Complex.one_re, conjTranspose_apply,
    Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]

theorem det_conj {p : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : Uᴴ * U = 1)
    (A : Matrix (Fin p) (Fin p) ℂ) : (Uᴴ * A * U).det = A.det := by
  have h := congrArg Matrix.det hU
  rw [Matrix.det_mul, Matrix.det_one] at h
  rw [Matrix.det_mul, Matrix.det_mul]
  linear_combination A.det * h

theorem posDef_conj {p : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : Uᴴ * U = 1)
    {A : Matrix (Fin p) (Fin p) ℂ} (hA : A.PosDef) : (Uᴴ * A * U).PosDef := by
  have hu : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact IsUnit.of_mul_eq_one_right _ h
  exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hu).2 hA

theorem row_lt_one {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : Uᴴ * U = 1)
    {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) (a : Fin p) :
    ∑ b, Complex.normSq ((Uᴴ * Z) a b) < 1 := by
  have h : 0 < (Uᴴ * (1 - Z * Zᴴ) * U : Matrix (Fin p) (Fin p) ℂ) a a := (posDef_conj U hU hZ).diag_pos
  have h1 := (Complex.lt_def.1 h).1
  rw [conj_diag U hU] at h1
  simp only [Complex.zero_re] at h1
  linarith

theorem rows_le_neg_log_det {p q : ℕ} (U : Matrix (Fin p) (Fin p) ℂ) (hU : Uᴴ * U = 1)
    {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    ∑ a, -Real.log (1 - ∑ b, Complex.normSq ((Uᴴ * Z) a b)) ≤
      -Real.log (1 - Z * Zᴴ).det.re := by
  have h := det_le_prod_diag (posDef_conj U hU hZ)
  rw [det_conj U hU] at h
  simp only [conj_diag U hU] at h
  have h2 := Real.log_le_log (ExhA.det_re_pos_im hZ).1 h
  rw [Real.log_prod (fun a _ => (sub_pos.2 (row_lt_one U hU hZ a)).ne')] at h2
  rw [Finset.sum_neg_distrib]
  linarith

theorem exists_unitary_rows {p q : ℕ} {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef) :
    ∃ U : Matrix (Fin p) (Fin p) ℂ, Uᴴ * U = 1 ∧
      -Real.log (1 - Z * Zᴴ).det.re =
        ∑ a, -Real.log (1 - ∑ b, Complex.normSq ((Uᴴ * Z) a b)) := by
  have hH := hZ.1
  have hU : (hH.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ)ᴴ * hH.eigenvectorUnitary = 1 :=
    Unitary.coe_star_mul_self hH.eigenvectorUnitary
  refine ⟨hH.eigenvectorUnitary, hU, ?_⟩
  have hdiag : (hH.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ)ᴴ * (1 - Z * Zᴴ) *
      (hH.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ) = Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    rwa [Unitary.conjStarAlgAut_star_apply] at this
  have hev : ∀ a, 1 - ∑ b, Complex.normSq
      (((hH.eigenvectorUnitary : Matrix (Fin p) (Fin p) ℂ)ᴴ * Z) a b) = hH.eigenvalues a := by
    intro a
    rw [← conj_diag _ hU, hdiag]
    simp
  have hd : (1 - Z * Zᴴ).det.re = ∏ i, hH.eigenvalues i := by
    rw [hH.det_eq_prod_eigenvalues]
    simp [← Complex.ofReal_prod]
  rw [hd, Real.log_prod (fun a _ => (hZ.eigenvalues_pos a).ne'), Finset.sum_neg_distrib]
  simp only [hev]

theorem neg_log_det_le {p q : ℕ} {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : (1 - Z * Zᴴ).PosDef)
    (hs : ∑ a, ∑ b, Complex.normSq (Z a b) ≤ 1 / 2) :
    -Real.log (1 - Z * Zᴴ).det.re ≤ 2 * ∑ a, ∑ b, Complex.normSq (Z a b) := by
  obtain ⟨U, hU, he⟩ := exists_unitary_rows hZ
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  have hF : ∑ a, ∑ b, Complex.normSq ((Uᴴ * Z) a b) = ∑ a, ∑ b, Complex.normSq (Z a b) := by
    rw [← RgC.trace_mul_conjTranspose_re, ← RgC.trace_mul_conjTranspose_re,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', Matrix.one_mul]
  rw [he, ← hF, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  set t := ∑ b, Complex.normSq ((Uᴴ * Z) a b) with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have ht1 : t ≤ 1 / 2 := by
    refine le_trans ?_ (hF ▸ hs)
    exact Finset.single_le_sum (f := fun a => ∑ b, Complex.normSq ((Uᴴ * Z) a b))
      (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ a)
  have h1 : 0 < 1 - t := by linarith
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : (1 - t)⁻¹ ≤ 1 + 2 * t := by
    rw [inv_le_iff_one_le_mul₀ h1]
    nlinarith
  linarith

end Matrices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rhF_eq_sum_re {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) :
    rhF X x0 z = ∑ τ, -Real.log (1 - ExF.Zt X z τ * (ExF.Zt X z τ)ᴴ).det.re := by
  rw [ExF.rhF_eq_sum X x0 ho, Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [ExF.norm_of_pos ((ExF.mem_OmF_iff X x0 ho z).1 hz τ).det_pos]
  rfl

theorem sharpAt_rhF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) : SharpAt (rhF X x0) z ξ := by
  have hpd : ∀ y ∈ OmF X x0, ∀ τ, (1 - ExF.Zt X y τ * (ExF.Zt X y τ)ᴴ).PosDef :=
    fun y hy => (ExF.mem_OmF_iff X x0 ho y).1 hy
  choose U hU he using fun τ => exists_unitary_rows (hpd z hz τ)
  have hS : SharpAt (fun y => ∑ τ, ∑ a, -Real.log (1 - ∑ b,
      Complex.normSq (((U τ)ᴴ * ExF.Zt X y τ) a b))) z ξ := by
    refine sharpAt_sum' fun τ => sharpAt_sum fun a => ?_
    refine sharpAt_ball (g := fun b y => ((U τ)ᴴ * ExF.Zt X y τ) a b) ξ (fun b => ?_)
      (row_lt_one _ (hU τ) (hpd z hz τ) a)
    simp only [Matrix.mul_apply]
    exact (ContDiff.sum fun c _ => contDiff_const.mul (ExF.cd_Zt X τ c b)).contDiffAt.of_le
      (WithTop.coe_le_coe.2 le_top)
  refine hS.of_minorant ((ExF.rhF_contDiffAt X x0 ho hz).of_le (WithTop.coe_le_coe.2 le_top)) ?_ ?_
  · filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with y hy
    rw [rhF_eq_sum_re X x0 ho hy]
    exact Finset.sum_le_sum fun τ _ => rows_le_neg_log_det _ (hU τ) (hpd y hy τ)
  · rw [rhF_eq_sum_re X x0 ho hz]
    exact Finset.sum_congr rfl fun τ _ => he τ

theorem continuous_inv_leadingBlock_entry {r : ℕ} (X : Data E r) (τ : X.Ψ) (a b : Fin X.p0) :
    Continuous fun z : V (nd X) => (ExF.n1 X z τ)⁻¹ a b := by
  simp only [ExF.unipotentFrame_inv_eq_adjugate]
  have h : Continuous fun z : V (nd X) => ExF.n1 X z τ :=
    continuous_pi fun i => continuous_pi fun j => (ExF.cd_nM X τ _ _).continuous
  exact h.matrix_adjugate.matrix_elem a b

theorem norm_Wm_sq_le {r : ℕ} (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (m : Fin (r - X.p0))
    (b : Fin X.p0) :
    ‖ExF.Wm X z τ m b‖ ^ 2 ≤ ∑ e : Ent X,
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2
      else 0 := by
  have hlt : Fin.castLE X.p0_le b < ExF.qI X m := by
    rw [Fin.lt_def]
    have := b.isLt
    simp only [ExF.qI, Fin.val_castLE]
    omega
  have h := Finset.single_le_sum (f := fun e : Ent X =>
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2
      else 0) (fun e _ => by split_ifs <;> positivity)
      (Finset.mem_univ (⟨τ, ⟨(ExF.qI X m, Fin.castLE X.p0_le b), hlt⟩⟩ : Ent X))
  refine le_trans (le_of_eq ?_) h
  have hc : ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0 ∧ X.p0 ≤ ((ExF.qI X m : Fin r) : ℕ) :=
    ⟨b.isLt, by simp [ExF.qI]⟩
  simp only [if_pos hc]
  simp [ExF.Wm, ExF.nM, mat, nmat, hlt]

theorem rhF_le_near_zero {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ∀ z : V (nd X), ‖z‖ < ρ → z ∈ OmF X x0 ∧ rhF X x0 z ≤ C * ∑ e : Ent X,
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2
      else 0 := by
  have hZ0 : ∀ τ, ExF.Zt X 0 τ = 0 := by
    intro τ
    have : ExF.Wm X 0 τ = 0 := by
      ext m b
      have h := norm_Wm_sq_le X 0 τ m b
      refine norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm (h.trans ?_) (by positivity)))
      refine le_of_eq (Finset.sum_eq_zero fun e _ => ?_)
      split_ifs
      · rw [show (0 : V (nd X)) (Fintype.equivFin (Ent X) e) = 0 from rfl]; simp
      · rfl
    simp [ExF.Zt, this]
  have h0 : (0 : V (nd X)) ∈ OmF X x0 := by
    rw [ExF.mem_OmF_iff X x0 ho]
    intro τ
    simp only [ExF.Am, hZ0, Matrix.zero_mul, sub_zero]
    exact Matrix.PosDef.one
  have e1 : ∀ᶠ z in 𝓝 (0 : V (nd X)), z ∈ OmF X x0 := (ExF.isOpen_OmF X x0).mem_nhds h0
  have e2 : ∀ᶠ z in 𝓝 (0 : V (nd X)), ∀ τ,
      ∑ a, ∑ b, Complex.normSq (ExF.Zt X z τ a b) < 1 / 2 := by
    rw [Filter.eventually_all]
    intro τ
    have hc : Continuous fun z : V (nd X) => ∑ a, ∑ b, Complex.normSq (ExF.Zt X z τ a b) :=
      continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        Complex.continuous_normSq.comp (ExF.cd_Zt X τ a b).continuous
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    simp [hZ0]
  have e3 : ∀ᶠ z in 𝓝 (0 : V (nd X)), ∀ τ b a,
      ‖(ExF.n1 X z τ)⁻¹ b a‖ < ‖(ExF.n1 X 0 τ)⁻¹ b a‖ + 1 := by
    simp only [Filter.eventually_all]
    intro τ b a
    exact (continuous_inv_leadingBlock_entry X τ b a).norm.continuousAt.eventually_lt continuousAt_const
      (lt_add_one _)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (e1.and (e2.and e3))
  refine ⟨ρ, ∑ τ, 2 * ∑ a, ∑ _m : Fin (r - X.p0),
    (∑ b, (‖(ExF.n1 X 0 τ)⁻¹ b a‖ + 1)) ^ 2, hρ, fun z hz => ?_⟩
  obtain ⟨hz1, hz2, hz3⟩ := hball (y := z) (by simpa using hz)
  refine ⟨hz1, ?_⟩
  set S := ∑ e : Ent X,
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2
      else 0 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun e _ => by split_ifs <;> positivity
  have hW : ∀ τ m b, ‖ExF.Wm X z τ m b‖ ≤ √S := fun τ m b =>
    Real.le_sqrt_of_sq_le (norm_Wm_sq_le X z τ m b)
  rw [rhF_eq_sum_re X x0 ho hz1, Finset.sum_mul]
  refine Finset.sum_le_sum fun τ _ => ?_
  refine (neg_log_det_le ((ExF.mem_OmF_iff X x0 ho z).1 hz1 τ) (hz2 τ).le).trans ?_
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun m _ => ?_
  have hn : ‖ExF.Zt X z τ a m‖ ≤ (∑ b, (‖(ExF.n1 X 0 τ)⁻¹ b a‖ + 1)) * √S := by
    rw [ExF.Zt, Matrix.transpose_apply, Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul (hz3 τ b a).le (hW τ m b) (norm_nonneg _) (by positivity)
  rw [Complex.normSq_eq_norm_sq]
  refine (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (le_of_eq ?_)
  rw [mul_pow, Real.sq_sqrt hS0]

theorem rhF_sharp_gradient : ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
    (∀ z ∈ OmF X x0, 0 ≤ rhF X x0 z ∧ ∀ ξ : Fin (nd X) → ℂ,
      Complex.normSq (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j) ≤ rhF X x0 z * leviRh X x0 z ξ) ∧
    ∃ ρ C : ℝ, 0 < ρ ∧ ∀ z : V (nd X), ‖z‖ < ρ → z ∈ OmF X x0 ∧ rhF X x0 z ≤ C * ∑ e : Ent X,
      if (e.2.1.2 : ℕ) < X.p0 ∧ X.p0 ≤ (e.2.1.1 : ℕ) then ‖z (Fintype.equivFin (Ent X) e)‖ ^ 2 else 0 :=
  fun _ X x0 ho =>
    ⟨fun _ hz => ⟨ExF.rhF_nonneg X x0 ho hz, fun ξ => (sharpAt_rhF X x0 ho hz ξ).2.2.2⟩,
      rhF_le_near_zero X x0 ho⟩

end GlobalTheory.SharpGradient

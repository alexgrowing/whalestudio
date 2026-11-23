import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero

set_option autoImplicit false

noncomputable section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
open scoped ComplexConjugate

namespace GlobalTheory.DefConst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def detPow (Ψ : Finset (E →+* ℂ)) (a : ℤ) (x : Frame Ψ r) : ℂ := ∏ τ, (mat x τ).det ^ a

theorem telescope : ∀ (n : ℕ) (f : Fin (n + 1) → ℝ), (∀ i, f i ≠ 0) →
    ∏ i : Fin n, f i.succ / f i.castSucc = f (Fin.last n) / f 0
  | 0, f, h => by
    rw [Fin.prod_univ_zero]; exact (div_self (h 0)).symm
  | n + 1, f, h => by
    rw [Fin.prod_univ_castSucc]
    have ih : ∏ i : Fin n, f i.succ.castSucc / f i.castSucc.castSucc =
        f (Fin.last n).castSucc / f (0 : Fin (n + 1)).castSucc :=
      telescope n (fun i => f i.castSucc) (fun i => h _)
    simp only [Fin.succ_castSucc]
    rw [ih, Fin.succ_last, Fin.castSucc_zero]
    have h1 := h (Fin.last n).castSucc
    have h2 := h 0
    field_simp

theorem lminor_zero (M : Matrix (Fin r) (Fin r) ℂ) : lminor M 0 = 1 := by
  unfold lminor
  exact Matrix.det_eq_one_of_card_eq_zero (by simp; exact Fintype.card_eq_zero)

theorem lminor_last (M : Matrix (Fin r) (Fin r) ℂ) : lminor M (Fin.last r) = M.det := by
  unfold lminor
  exact Matrix.det_submatrix_equiv_self (finCongr (Fin.val_last r)) M

theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = x.transpose * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G x).det = x.det * (G.map τ).det * starRingEnd ℂ x.det := by
  rw [gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  congr 1
  exact (RingHom.map_det (starRingEnd ℂ) x).symm

theorem dmin_ne (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i ≠ 0 := by
  intro h
  have := (hx τ).2 i
  rw [h] at this
  simp at this

theorem pnorm_factor (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (a : ℤ) (τ : X.Ψ) :
    ‖(mat x τ).det ^ a‖ * ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) =
      ‖(X.Gm.map τ.1).det‖ ^ (-(a : ℝ) / 2) := by
  have hD : (mat x τ).det ≠ 0 := (hx τ).1
  have hpos : 0 < ‖(mat x τ).det‖ := norm_pos_iff.mpr hD
  have ht := telescope r (fun i => ‖dmin X.Gm x τ i‖) (fun i => norm_ne_zero_iff.mpr (dmin_ne X hx τ i))
  beta_reduce at ht
  have hprod : ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(a : ℝ) / 2) =
      (‖dmin X.Gm x τ (Fin.last r)‖ / ‖dmin X.Gm x τ 0‖) ^ (-(a : ℝ) / 2) := by
    simp_rw [norm_div]
    rw [Real.finset_prod_rpow _ _ (fun i _ => by positivity), ht]
  rw [hprod]
  have h0 : dmin X.Gm x τ 0 = 1 := lminor_zero _
  have hl : dmin X.Gm x τ (Fin.last r) = (mat x τ).det * (X.Gm.map τ.1).det * starRingEnd ℂ (mat x τ).det := by
    unfold dmin; rw [lminor_last, det_gram]
  rw [h0, hl, norm_one, div_one, norm_mul, norm_mul, Complex.norm_conj, norm_zpow]
  have hg : 0 ≤ ‖(X.Gm.map τ.1).det‖ := norm_nonneg _
  rw [show ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ * ‖(mat x τ).det‖ =
      ‖(mat x τ).det‖ * ‖(mat x τ).det‖ * ‖(X.Gm.map τ.1).det‖ by ring,
    Real.mul_rpow (by positivity) hg, Real.mul_rpow hpos.le hpos.le, ← Real.rpow_intCast,
    ← mul_assoc, ← mul_assoc, ← Real.rpow_add hpos, ← Real.rpow_add hpos]
  have : (a : ℝ) + -(a : ℝ) / 2 + -(a : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

theorem pnorm_detPow (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) (a : ℤ)
    (hla : ∀ τ i, la τ i = a) :
    X.pnorm la (detPow X.Ψ a) x = ∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖ ^ (-(a : ℝ) / 2) := by
  unfold Data.pnorm detPow
  simp only [hla, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => pnorm_factor X hx a τ

theorem det_diff (Ψ : Finset (E →+* ℂ)) (τ : Ψ) : Differentiable ℂ (fun x : Frame Ψ r => (mat x τ).det) := by
  simp only [Matrix.det_apply', mat, Matrix.of_apply]
  fun_prop

theorem detPow_diff (X : Data E r) (a : ℤ) : DifferentiableOn ℂ (detPow X.Ψ a) X.dom := by
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  unfold detPow
  have h : ∀ τ : X.Ψ, DifferentiableAt ℂ (fun y : Frame X.Ψ r => (mat y τ).det ^ a) x :=
    fun τ => (det_diff X.Ψ τ x).zpow (Or.inl (hx τ).1)
  fun_prop

theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact 1 x = x := by
  funext τ
  simp [lact, mat, Matrix.map_one]
  rfl

theorem chi_one (X : Data E r) (la : Wt X.Ψ r) : X.χ la 1 = 1 := by
  have h1 : (1 : GL (Fin r) E) ∈ X.Γ := X.Γ.one_mem
  have hm := X.χ_mul la 1 h1 1 h1
  rw [mul_one] at hm
  obtain ⟨n, hn, hf⟩ := X.χ_fin la
  have hne : X.χ la 1 ≠ 0 := fun h0 => by
    have := hf 1 h1
    rw [h0, zero_pow hn.ne'] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hne (hm.symm.trans (mul_one _).symm)

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P : Matrix (Fin r) (Fin r) ℂ)
    (v w : Fin r → ℂ) :
    hermC τ G (P.mulVec v) (P.mulVec w) = ∑ k, ∑ l, v k * gram τ G P k l * conj (w l) := by
  have sw : ∀ f : Fin r → Fin r → Fin r → Fin r → ℂ,
      ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := by
    intro f
    calc ∑ a, ∑ b, ∑ k, ∑ l, f a b k l = ∑ a, ∑ k, ∑ b, ∑ l, f a b k l :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ b, ∑ l, f a b k l := Finset.sum_comm
      _ = ∑ k, ∑ a, ∑ l, ∑ b, f a b k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ a, ∑ b, f a b k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  simp only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct]
  calc _ = ∑ a, ∑ b, ∑ k, ∑ l, P a k * v k * τ (G a b) * conj (P b l * w l) := by
        simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, P a k * v k * τ (G a b) * conj (P b l * w l) := sw _
    _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [map_mul]; ring

theorem not_iso (X : Data E r) (hp : X.p0 = 0 ∨ X.p0 = r) (ξ : Fin r → E) : ¬ X.IsIso ξ := by
  rintro ⟨-, h0, hne⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : E →+* ℂ, τ ∈ X.Ψ := by
    let τ0 : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate τ0, (X.cmType _).2 ?_⟩
      simpa using h
  obtain ⟨P, hP, hg⟩ := X.signature ⟨τ, hτ⟩
  set u : Fin r → ℂ := fun a => τ (ξ a) with hu_def
  have hu : hermC τ X.Gm u u = 0 := by
    have := congrArg τ h0
    simp only [herm, cc, map_sum, map_mul, map_zero, IsCMField.complexEmbedding_complexConj] at this
    simpa [hermC, u] using this
  obtain ⟨e, he, hsg⟩ : ∃ e : ℂ, e ≠ 0 ∧ ∀ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) = e := by
    rcases hp with h | h
    · exact ⟨-1, by norm_num, fun a => by simp [sgn, h]⟩
    · exact ⟨1, one_ne_zero, fun a => by simp [sgn, h, a.isLt]⟩
  set v := P⁻¹.mulVec u with hv_def
  have hPv : P.mulVec v = u := by
    rw [hv_def, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP), Matrix.one_mulVec]
  have hsum : hermC τ X.Gm u u = e * ∑ a, v a * conj (v a) := by
    rw [← hPv, hermC_mulVec, hg]
    simp only [Matrix.diagonal_apply, hsg, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hv : v = 0 := by
    have h1 : ∑ a, (Complex.normSq (v a) : ℂ) = 0 := by
      have := hsum.symm.trans hu
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h he
      · simpa [Complex.mul_conj] using h
    have h2 : ∑ a, Complex.normSq (v a) = 0 := by exact_mod_cast h1
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)] at h2
    funext a
    simpa using h2 a (Finset.mem_univ _)
  have hu0 : u = 0 := by rw [← hPv, hv, Matrix.mulVec_zero]
  apply hne
  funext a
  have := congrFun hu0 a
  simpa [u] using this

theorem detPow_mem_SS (X : Data E r) (hΓ : ∀ γ ∈ X.Γ, γ = 1) (hdef : ∀ ξ, ¬ X.IsIso ξ) (la : Wt X.Ψ r)
    (a : ℤ) (hla : ∀ τ i, la τ i = a) : detPow X.Ψ a ∈ X.SS la := by
  refine ⟨⟨⟨detPow_diff X a, ?_, ?_⟩, ⟨_, fun x hx => (pnorm_detPow X hx la a hla).le⟩⟩,
    fun ξ hξ => absurd hξ (hdef ξ)⟩
  · intro x _ b hb
    unfold detPow bchar
    have hb' : ∀ τ : X.Ψ, (mat b τ).det = ∏ i, b τ i i := fun τ =>
      Matrix.det_of_upperTriangular (fun i j hij => (hb τ).2 i j hij)
    have e1 : ∀ τ : X.Ψ, (mat (rmul x b) τ).det ^ a = (mat x τ).det ^ a * ∏ i, b τ i i ^ la τ i := by
      intro τ
      rw [show mat (rmul x b) τ = mat x τ * mat b τ from rfl, Matrix.det_mul, mul_zpow, hb' τ]
      simp only [hla]
      rw [Finset.prod_zpow]
    simp only [e1, Finset.prod_mul_distrib]
    ring
  · intro γ hγ x _
    rw [hΓ γ hγ, lact_one, chi_one, one_mul]

theorem exists_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ γ ∈ X.Γ, γ = 1) → (X.p0 = 0 ∨ X.p0 = r) → ∀ s : ℕ, ∀ x ∈ X.dom,
      ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x ≠ 0 := by
  intro E _ _ _ r X hΓ hp s x hx
  refine ⟨detPow X.Ψ (if X.p0 = 0 then ((s / 2 : ℕ) : ℤ) else -((s / 2 : ℕ) : ℤ)),
    detPow_mem_SS X hΓ (not_iso X hp) _ _ ?_, ?_⟩
  · intro τ i
    by_cases h0 : X.p0 = 0
    · simp [deMul, h0]
    · have h : X.p0 = r := hp.resolve_left h0
      have hr : r ≠ 0 := h ▸ h0
      simp [deMul, h0, h, hr, i.isLt]
  · exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ).1

end GlobalTheory.DefConst

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfHermOne

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix

namespace GlobalTheory.TwoLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def colSq {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) (τ : Ψ) : ℝ :=
  ‖x τ 0 0‖ ^ 2 + ‖x τ 1 0‖ ^ 2

noncomputable def idx (X : Data E 2) (τ : X.Ψ) : Fin (nd X) :=
  Fintype.equivFin (Ent X) ⟨τ, ⟨(1, 0), by decide⟩⟩

theorem idx_injective (X : Data E 2) : Function.Injective (idx X) := fun _ _ h =>
  congrArg Prod.fst ((Fintype.equivFin (Ent X)).injective h)

theorem idx_surjective (X : Data E 2) : Function.Surjective (idx X) := by
  intro k
  obtain ⟨⟨τ, ⟨⟨a, b⟩, h⟩⟩, rfl⟩ := (Fintype.equivFin (Ent X)).surjective k
  refine ⟨τ, ?_⟩
  have : a = 1 ∧ b = 0 := by revert a b; decide
  obtain ⟨rfl, rfl⟩ := this
  rfl

theorem compact_frame_first_column (X : Data E 2) (x0 : Frame X.Ψ 2) (z : V (nd X)) (τ : X.Ψ) (a : Fin 2) :
    cpt X x0 z τ a 0 = x0 τ a 0 + x0 τ a 1 * z (idx X τ) := by
  show (mat x0 τ * mat (nmat X z) τ) a 0 = _
  simp [Matrix.mul_apply, mat, nmat, idx]

theorem compact_frame_second_column (X : Data E 2) (x0 : Frame X.Ψ 2) (z : V (nd X)) (τ : X.Ψ) (a : Fin 2) :
    cpt X x0 z τ a 1 = x0 τ a 1 := by
  show (mat x0 τ * mat (nmat X z) τ) a 1 = _
  simp [Matrix.mul_apply, mat, nmat]

omit [NumberField E] [IsCMField E] in
theorem det_mat {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) (τ : Ψ) :
    (mat x τ).det = x τ 0 0 * x τ 1 1 - x τ 0 1 * x τ 1 0 := by
  simp [Matrix.det_fin_two, mat]

theorem det_cpt (X : Data E 2) (x0 : Frame X.Ψ 2) (z : V (nd X)) (τ : X.Ψ) :
    (mat (cpt X x0 z) τ).det = (mat x0 τ).det := by
  simp only [det_mat, compact_frame_first_column, compact_frame_second_column]; ring

omit [NumberField E] [IsCMField E] in
theorem right_mul_borel_first_column {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) {b : Frame Ψ 2} (hb : b ∈ Bor Ψ 2) (τ : Ψ)
    (a : Fin 2) : rmul x b τ a 0 = b τ 0 0 * x τ a 0 := by
  show (mat x τ * mat b τ) a 0 = _
  have := (hb τ).2 1 0 (by decide)
  simp [Matrix.mul_apply, mat, this, mul_comm]

omit [NumberField E] [IsCMField E] in
theorem bor_ne {Ψ : Finset (E →+* ℂ)} {b : Frame Ψ 2} (hb : b ∈ Bor Ψ 2) (τ : Ψ) : b τ 0 0 ≠ 0 := by
  intro h
  apply (hb τ).1
  rw [det_mat, h, (hb τ).2 1 0 (by decide)]; ring

omit [NumberField E] [IsCMField E] in
theorem lact_one' {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) : lact (1 : GL (Fin 2) E) x = x := by
  funext τ
  simp [lact]
  rfl

omit [NumberField E] [IsCMField E] in
theorem gram_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) (τ : Ψ) (a b : Fin 2) :
    gram τ.1 1 (mat x τ) a b = x τ 0 a * conj (x τ 0 b) + x τ 1 a * conj (x τ 1 b) := by
  simp [gram, hermC, col, mat, Matrix.one_apply]

omit [NumberField E] [IsCMField E] in
theorem dmin_0 {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) (τ : Ψ) : dmin 1 x τ 0 = 1 := by
  simp [dmin, lminor, Matrix.det_isEmpty]

omit [NumberField E] [IsCMField E] in
theorem dmin_1 {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) (τ : Ψ) : dmin 1 x τ 1 = (colSq x τ : ℝ) := by
  have : dmin 1 x τ 1 = gram τ.1 1 (mat x τ) 0 0 := Matrix.det_fin_one _
  rw [this, gram_one, Complex.mul_conj, Complex.mul_conj, colSq,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast; ring

omit [NumberField E] [IsCMField E] in
theorem dmin_2 {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ 2) (τ : Ψ) :
    dmin 1 x τ 2 = (‖(mat x τ).det‖ ^ 2 : ℝ) := by
  have : dmin 1 x τ 2 = gram τ.1 1 (mat x τ) 0 0 * gram τ.1 1 (mat x τ) 1 1 -
      gram τ.1 1 (mat x τ) 0 1 * gram τ.1 1 (mat x τ) 1 0 := Matrix.det_fin_two _
  rw [this, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, det_mat]
  simp only [gram_one, map_sub, map_mul]
  ring

omit [NumberField E] [IsCMField E] in
theorem colSq_pos {Ψ : Finset (E →+* ℂ)} {x : Frame Ψ 2} {τ : Ψ} (h : (mat x τ).det ≠ 0) :
    0 < colSq x τ := by
  rw [det_mat] at h
  by_contra hn
  have h0 : x τ 0 0 = 0 := by
    rw [← norm_eq_zero]; unfold colSq at hn; nlinarith [sq_nonneg ‖x τ 0 0‖, sq_nonneg ‖x τ 1 0‖]
  have h1 : x τ 1 0 = 0 := by
    rw [← norm_eq_zero]; unfold colSq at hn; nlinarith [sq_nonneg ‖x τ 0 0‖, sq_nonneg ‖x τ 1 0‖]
  apply h
  rw [h0, h1]; ring

theorem mem_dom {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) (x : Frame X.Ψ 2) :
    x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0 := by
  refine ⟨fun h τ => (h τ).1, fun h τ => ⟨h τ, fun i => ?_⟩⟩
  rw [hG, hp]
  fin_cases i
  · simp [psgn, dmin_0]
  · simpa [psgn, sgn, dmin_1] using colSq_pos (h τ)
  · have := h τ
    simp only [Fin.reduceFinMk, dmin_2, Complex.ofReal_re]
    simp [psgn, sgn, Finset.prod_range_succ, this]

theorem cpt_mem {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) {x0 : Frame X.Ψ 2} (h : x0 ∈ X.dom)
    (z : V (nd X)) : cpt X x0 z ∈ X.dom := by
  rw [mem_dom hG hp] at h ⊢
  intro τ; rw [det_cpt]; exact h τ

theorem pnorm_sq {X : Data E 2} (hG : X.Gm = 1) {x : Frame X.Ψ 2} (hx : x ∈ X.dom) {la : Wt X.Ψ 2}
    {m : ℕ} (h0 : ∀ τ, la τ 0 = m) (h1 : ∀ τ, la τ 1 = 0) (P : Frame X.Ψ 2 → ℂ) :
    X.pnorm la P x ^ 2 = ‖P x‖ ^ 2 / (∏ τ, colSq x τ) ^ m := by
  unfold Data.pnorm
  rw [mul_pow, div_eq_mul_inv, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hp := colSq_pos (hx τ).1
  rw [Fin.prod_univ_two, h0, h1, hG]
  have e1 : (0 : Fin 2).succ = 1 := rfl
  have e2 : (0 : Fin 2).castSucc = 0 := rfl
  rw [e1, e2, dmin_0, dmin_1]
  simp only [Int.cast_zero, neg_zero, zero_div, Real.rpow_zero, mul_one, div_one, Complex.norm_real,
    Real.norm_of_nonneg hp.le, Int.cast_natCast]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, ← Real.rpow_natCast, ← Real.rpow_neg hp.le]
  congr 1
  push_cast; ring

theorem phla_cpt {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) {x0 : Frame X.Ψ 2} (hx : x0 ∈ X.dom)
    (la : Wt X.Ψ 2) (z : V (nd X)) :
    phla X la (cpt X x0 z) = ∑ τ, ((la τ 0 - la τ 1 : ℝ) * Real.log (colSq (cpt X x0 z) τ) +
      (la τ 1 : ℝ) * Real.log (‖(mat x0 τ).det‖ ^ 2)) := by
  rw [IW.phla_eq X (cpt_mem hG hp hx z)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hc := colSq_pos (cpt_mem hG hp hx z τ).1
  have e1 : (0 : Fin 2).succ = 1 := rfl
  have e2 : (0 : Fin 2).castSucc = 0 := rfl
  have e3 : (1 : Fin 2).succ = 2 := rfl
  have e4 : (1 : Fin 2).castSucc = 1 := rfl
  rw [Fin.sum_univ_two, e1, e2, e3, e4]
  simp only [IW.Lm, hG, dmin_0, dmin_1, dmin_2, det_cpt, Complex.norm_real, Real.norm_of_nonneg hc.le,
    norm_one, Real.log_one, Real.norm_of_nonneg (sq_nonneg ‖(mat x0 τ).det‖)]
  ring

theorem not_isIso {X : Data E 2} (hG : X.Gm = 1) (ξ : Fin 2 → E) : ¬ X.IsIso ξ := fun h =>
  h.2.2 (eq_zero_of_herm_one ξ (hG ▸ h.2.1))

theorem chi_one (X : Data E 2) (la : Wt X.Ψ 2) : X.χ la 1 = 1 := by
  have h1 := X.χ_mul la 1 X.Γ.one_mem 1 X.Γ.one_mem
  obtain ⟨n, hn, h2⟩ := X.χ_fin la
  have h3 := h2 1 X.Γ.one_mem
  have h4 : X.χ la 1 ≠ 0 := by
    intro h; rw [h, zero_pow hn.ne'] at h3; exact zero_ne_one h3
  rw [mul_one] at h1
  exact (mul_eq_left₀ h4).1 h1.symm

theorem mem_SSgt {X : Data E 2} (hG : X.Gm = 1) (hΓ : X.Γ = ⊥) {la : Wt X.Ψ 2}
    {m : ℕ} (h0 : ∀ τ, la τ 0 = m) (h1 : ∀ τ, la τ 1 = 0) {P : Frame X.Ψ 2 → ℂ}
    (hd : Differentiable ℂ P)
    (he : ∀ x, ∀ b ∈ Bor X.Ψ 2, P (rmul x b) = (∏ τ, b τ 0 0) ^ m * P x)
    {C : ℝ} (hb : ∀ x, ‖P x‖ ^ 2 ≤ C * (∏ τ, colSq x τ) ^ m) (c : ℝ) : P ∈ X.SSgt la c := by
  refine ⟨⟨⟨⟨hd.differentiableOn, fun x _ b hb => ?_, fun γ hγ x _ => ?_⟩, ⟨√C, fun x hx => ?_⟩⟩,
    fun ξ h => (not_isIso hG ξ h).elim⟩, fun ξ h => (not_isIso hG ξ h).elim⟩
  · rw [he x b hb, bchar, ← Finset.prod_pow]
    simp [Fin.prod_univ_two, h0, h1]
  · rw [hΓ, Subgroup.mem_bot] at hγ
    rw [hγ, chi_one, lact_one', one_mul]
  · apply Real.le_sqrt_of_sq_le
    rw [pnorm_sq hG hx h0 h1, div_le_iff₀ (pow_pos (Finset.prod_pos fun τ _ => colSq_pos (hx τ).1) _)]
    exact hb x

theorem isCompact_orth {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) :
    IsCompact {x : Frame X.Ψ 2 | IsOrth X x} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : {x : Frame X.Ψ 2 | IsOrth X x} = ⋂ τ, ⋂ a, ⋂ b, {x | x τ 0 a * conj (x τ 0 b) +
        x τ 1 a * conj (x τ 1 b) =
          Matrix.diagonal (fun a : Fin 2 => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) a b} := by
      ext x
      simp only [IsOrth, hG, ← Matrix.ext_iff, gram_one, Set.mem_iInter]
      rfl
    rw [this]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_eq ?_ continuous_const
    fun_prop
  · refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ 2)) (r := 1)).subset fun x hx => ?_
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ => (pi_norm_le_iff_of_nonneg zero_le_one).2
      fun a => (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_
    have h := congrFun (congrFun (hx τ) b) b
    rw [hG, gram_one, hp, Matrix.diagonal_apply_eq, Complex.mul_conj, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, sgn, if_pos b.2] at h
    have h' : ‖x τ 0 b‖ ^ 2 + ‖x τ 1 b‖ ^ 2 = 1 := by exact_mod_cast h
    have h4 : ‖x τ a b‖ ^ 2 ≤ 1 := by
      fin_cases a
      · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ‖x τ 1 b‖]
      · simp only [Fin.mk_one]; nlinarith [sq_nonneg ‖x τ 0 b‖]
    nlinarith [norm_nonneg (x τ a b)]

end GlobalTheory.TwoLines

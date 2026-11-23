import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientCurvatureStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaZeroOneSkewConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaZeroOneLowerVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineGramCurvatureFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineGramCurvatureAllFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartWeightCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagWeightGramCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVanishOnFiberTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFlagFrameExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineChernProductSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightNormSqSmoothPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGramPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameFlagCurvatureStatement

open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.GradedLines

section Helpers
variable {V : Type*}

theorem diagVal_real_mul (c : ℝ) (α : V → V → ℂ) (ξ : V) :
    diagVal (fun ξ η => (c : ℂ) * α ξ η) ξ = c * diagVal α ξ := by
  simp only [diagVal]; rw [mul_left_comm, re_ofReal_mul]

theorem diagVal_zero (ξ : V) : diagVal (fun _ _ => (0 : ℂ)) ξ = 0 := by simp [diagVal]

end Helpers

section Vert
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] {n : ℕ}

theorem diagVal_vertForm (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ) (y ξ : E) :
    diagVal (vertForm H π e lam y) ξ = 1 / (2 * Real.pi) * ∑ i, ∑ l ∈ Finset.Ioi i,
      (lam i - lam l) * Complex.normSq (thetaOneZero H π e y ξ l i) := by
  have hk : -I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa]; push_cast; field_simp; rw [I_sq]; ring
  simp only [diagVal, vertForm, thetaSq, ← mul_assoc, hk, mul_conj, ← ofReal_mul,
    ← ofReal_sum, Finset.mul_sum, re_ofReal_mul]
  simp [Complex.re_sum, ← ofReal_mul]

theorem vertForm_nonneg (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) {lam : Fin n → ℝ} (h : Antitone lam) (y : E) :
    FormLe (fun _ _ => 0) (vertForm H π e lam y) := fun ξ => by
  rw [diagVal_zero, diagVal_vertForm]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun l hl => ?_)
  exact mul_nonneg (sub_nonneg.2 (h (Finset.mem_Ioi.1 hl).le)) (Complex.normSq_nonneg _)

theorem vertForm_pos (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) {lam : Fin n → ℝ} (h : StrictAnti lam) (y ξ : E)
    (hne : ∃ i l, i < l ∧ thetaOneZero H π e y ξ l i ≠ 0) :
    0 < diagVal (vertForm H π e lam y) ξ := by
  obtain ⟨i, l, hil, hθ⟩ := hne
  rw [diagVal_vertForm]
  refine mul_pos (by positivity) ?_
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun l hl => mul_nonneg
    (sub_nonneg.2 (h.antitone (Finset.mem_Ioi.1 hl).le)) (Complex.normSq_nonneg _)) ⟨i, Finset.mem_univ _, ?_⟩
  refine Finset.sum_pos' (fun l hl => mul_nonneg
    (sub_nonneg.2 (h.antitone (Finset.mem_Ioi.1 hl).le)) (Complex.normSq_nonneg _))
    ⟨l, Finset.mem_Ioi.2 hil, mul_pos (sub_pos.2 (h hil)) (Complex.normSq_pos.2 hθ)⟩

end Vert

theorem lineChern_mul' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (f g : E → ℝ) (y : E) (hf : ContDiffAt ℝ 2 f y)
    (hg : ContDiffAt ℝ 2 g y) (hf0 : 0 < f y) (hg0 : 0 < g y) (ξ η : E) :
    lineChern (fun x => f x * g x) y ξ η = lineChern f y ξ η + lineChern g y ξ η := by
  have := GlobalTheory.T.line_chern_product_sum E (Fin 2) ![f, g] y (fun τ => by fin_cases τ <;> simpa) (fun τ => by fin_cases τ <;> simpa) ξ η
  simpa [Fin.prod_univ_two, Fin.sum_univ_two] using this

theorem glc : GradedLineCurvature := by
  intro E _ _ _ _ _ ι _ n U H Y π A e hH hA he y hy
  refine ⟨GlobalTheory.T.theta_zero_one_skew_conj E ι n U H Y π A e hH hA he y hy, GlobalTheory.T.theta_zero_one_lower_vanish E ι n U H Y π A e hH hA he y hy,
    GlobalTheory.T.line_gram_curvature_formula E ι n U H Y π A e hH hA he y hy, fun lam => ⟨GlobalTheory.T.lineChern_weightNormSq_eq_vertForm_add_horizForm E ι n U H Y π A e hH hA he y hy
      (GlobalTheory.T.line_gram_curvature_formula E ι n U H Y π A e hH hA he y hy) lam, fun h => vertForm_nonneg H π e h y,
      GlobalTheory.T.flag_chart_weight_curvature E ι n U H Y π A e hH hA he y hy lam, GlobalTheory.T.flag_weight_gram_curvature E ι n U H Y π A e hH hA he y hy lam⟩⟩

theorem clb : ChernLowerBound := by
  intro E _ _ _ _ _ ι _ T _ p q U HW Hω Y π AW Aω G C hW hω hAW hAω hbW hbω lam hlW hlω y hy ξ
  choose eW heW using fun τ => GlobalTheory.T.unitary_flag_frame_exists E ι (p τ) U (HW τ) Y π (AW τ) (hW τ) (hAW τ)
  choose eω heω using fun τ => GlobalTheory.T.unitary_flag_frame_exists E ι (q τ) U (Hω τ) Y π (Aω τ) (hω τ) (hAω τ)
  set lW : ∀ τ, Fin (p τ) → ℝ := fun τ i => lam τ (Fin.castAdd (q τ) i) with hlWdef
  set lω : ∀ τ, Fin (q τ) → ℝ := fun τ i => lam τ (Fin.natAdd (p τ) i) with hlωdef
  have sW := fun τ => GlobalTheory.T.weight_norm_sq_smooth_pos E ι (p τ) U (HW τ) Y π (AW τ) (hW τ) (hAW τ) y hy (lW τ)
  have sω := fun τ => GlobalTheory.T.weight_norm_sq_smooth_pos E ι (q τ) U (Hω τ) Y π (Aω τ) (hω τ) (hAω τ) y hy (lω τ)
  have key : lineChern (pairWeightNormSq HW Hω π AW Aω lam) y = fun ξ η => ∑ τ,
      ((vertForm (HW τ) π (eW τ) (lW τ) y ξ η + horizForm (HW τ) π (eW τ) (lW τ) y ξ η) +
       (vertForm (Hω τ) π (eω τ) (lω τ) y ξ η + horizForm (Hω τ) π (eω τ) (lω τ) y ξ η)) := by
    funext ξ η
    rw [show pairWeightNormSq HW Hω π AW Aω lam = fun x => ∏ τ,
      (fun τ x => weightNormSq (HW τ) π (AW τ) (lW τ) x * weightNormSq (Hω τ) π (Aω τ) (lω τ) x) τ x
      from rfl]
    rw [GlobalTheory.T.line_chern_product_sum E T _ y (fun τ => (sW τ).1.mul (sω τ).1) (fun τ => mul_pos (sW τ).2 (sω τ).2)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [lineChern_mul' _ _ y (sW τ).1 (sω τ).1 (sW τ).2 (sω τ).2,
      GlobalTheory.T.lineChern_weightNormSq_eq_vertForm_add_horizForm E ι (p τ) U (HW τ) Y π (AW τ) (eW τ) (hW τ) (hAW τ) (heW τ) y hy
        (GlobalTheory.T.line_gram_curvature_formula E ι (p τ) U (HW τ) Y π (AW τ) (eW τ) (hW τ) (hAW τ) (heW τ) y hy),
      GlobalTheory.T.lineChern_weightNormSq_eq_vertForm_add_horizForm E ι (q τ) U (Hω τ) Y π (Aω τ) (eω τ) (hω τ) (hAω τ) (heω τ) y hy
        (GlobalTheory.T.line_gram_curvature_formula E ι (q τ) U (Hω τ) Y π (Aω τ) (eω τ) (hω τ) (hAω τ) (heω τ) y hy)]
  have hsum : diagVal (lineChern (pairWeightNormSq HW Hω π AW Aω lam) y) ξ = ∑ τ,
      ((diagVal (vertForm (HW τ) π (eW τ) (lW τ) y) ξ + diagVal (horizForm (HW τ) π (eW τ) (lW τ) y) ξ) +
       (diagVal (vertForm (Hω τ) π (eω τ) (lω τ) y) ξ + diagVal (horizForm (Hω τ) π (eω τ) (lω τ) y) ξ)) := by
    rw [key]; simp only [diagVal, mul_add, Finset.mul_sum, Complex.add_re, Complex.re_sum]
  rw [hsum, diagVal_real_mul]
  set dp := diagVal (pullForm G π y) ξ
  have hl : (-(C / (2 * Real.pi)) * ∑ τ, ∑ i, |lam τ i|) * dp = ∑ τ,
      (-(1 / (2 * Real.pi) * (∑ i, |lW τ i|) * C * dp) +
        -(1 / (2 * Real.pi) * (∑ i, |lω τ i|) * C * dp)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fin.sum_univ_add]; simp only [lW, lω]; ring
  rw [hl]
  refine Finset.sum_le_sum fun τ _ => add_le_add ?_ ?_
  · have h1 := (abs_le.1 (formAbsLe_iff.1 (GlobalTheory.T.flag_weight_gram_curvature E ι (p τ) U (HW τ) Y π (AW τ) (eW τ) (hW τ) (hAW τ)
      (heW τ) y hy (lW τ) G C (hbW τ)) ξ)).1
    have h2 := vertForm_nonneg (HW τ) π (eW τ) (hlW τ) y ξ
    rw [diagVal_zero] at h2
    linarith
  · have h1 := (abs_le.1 (formAbsLe_iff.1 (GlobalTheory.T.flag_weight_gram_curvature E ι (q τ) U (Hω τ) Y π (Aω τ) (eω τ) (hω τ) (hAω τ)
      (heω τ) y hy (lω τ) G C (hbω τ)) ξ)).1
    have h2 := vertForm_nonneg (Hω τ) π (eω τ) (hlω τ) y ξ
    rw [diagVal_zero] at h2
    linarith

theorem hp : HodgePositivity := by
  intro E _ _ _ _ _ ι _ T _ p q U ψ a b Y π AW Aω hψ ha hb hAW hAω lam y hy
  have hP := fun τ => GlobalTheory.T.hodge_frame_gram_positive ι (p τ) (q τ) U (ψ τ) (a τ) (b τ) (hψ τ) (ha τ) (hb τ)
  choose eW heW using fun τ => GlobalTheory.T.unitary_flag_frame_exists E ι (p τ) U _ Y π (AW τ) (hP τ).1 (hAW τ)
  choose eω heω using fun τ => GlobalTheory.T.unitary_flag_frame_exists E ι (q τ) U _ Y π (Aω τ) (hP τ).2 (hAω τ)
  set HW : ∀ τ, (ι → ℂ) → Matrix (Fin (p τ)) (Fin (p τ)) ℂ :=
    fun τ x => (a τ : ℂ) • quotGram (ψ τ x) with hHW
  set Hω : ∀ τ, (ι → ℂ) → Matrix (Fin (q τ)) (Fin (q τ)) ℂ :=
    fun τ x => (b τ : ℂ) • -subGram (ψ τ x) with hHω
  set lW : ∀ τ, Fin (p τ) → ℝ := fun τ i => lam τ (Fin.castAdd (q τ) i) with hlWdef
  set lω : ∀ τ, Fin (q τ) → ℝ := fun τ i => lam τ (Fin.natAdd (p τ) i) with hlωdef
  have sW := fun τ => GlobalTheory.T.weight_norm_sq_smooth_pos E ι (p τ) U (HW τ) Y π (AW τ) (hP τ).1 (hAW τ) y hy (lW τ)
  have sω := fun τ => GlobalTheory.T.weight_norm_sq_smooth_pos E ι (q τ) U (Hω τ) Y π (Aω τ) (hP τ).2 (hAω τ) y hy (lω τ)
  have key : lineChern (pairWeightNormSq HW Hω π AW Aω lam) y = fun ξ η => ∑ τ,
      ((vertForm (HW τ) π (eW τ) (lW τ) y ξ η + horizForm (HW τ) π (eW τ) (lW τ) y ξ η) +
       (vertForm (Hω τ) π (eω τ) (lω τ) y ξ η + horizForm (Hω τ) π (eω τ) (lω τ) y ξ η)) := by
    funext ξ η
    rw [show pairWeightNormSq HW Hω π AW Aω lam = fun x => ∏ τ,
      (fun τ x => weightNormSq (HW τ) π (AW τ) (lW τ) x * weightNormSq (Hω τ) π (Aω τ) (lω τ) x) τ x
      from rfl]
    rw [GlobalTheory.T.line_chern_product_sum E T _ y (fun τ => (sW τ).1.mul (sω τ).1) (fun τ => mul_pos (sW τ).2 (sω τ).2)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [lineChern_mul' _ _ y (sW τ).1 (sω τ).1 (sW τ).2 (sω τ).2,
      GlobalTheory.T.lineChern_weightNormSq_eq_vertForm_add_horizForm E ι (p τ) U (HW τ) Y π (AW τ) (eW τ) (hP τ).1 (hAW τ) (heW τ) y hy
        (GlobalTheory.T.line_gram_curvature_formula E ι (p τ) U (HW τ) Y π (AW τ) (eW τ) (hP τ).1 (hAW τ) (heW τ) y hy),
      GlobalTheory.T.lineChern_weightNormSq_eq_vertForm_add_horizForm E ι (q τ) U (Hω τ) Y π (Aω τ) (eω τ) (hP τ).2 (hAω τ) (heω τ) y hy
        (GlobalTheory.T.line_gram_curvature_formula E ι (q τ) U (Hω τ) Y π (Aω τ) (eω τ) (hP τ).2 (hAω τ) (heω τ) y hy)]
  have hsum : ∀ ξ, diagVal (lineChern (pairWeightNormSq HW Hω π AW Aω lam) y) ξ = ∑ τ,
      ((diagVal (vertForm (HW τ) π (eW τ) (lW τ) y) ξ + diagVal (horizForm (HW τ) π (eW τ) (lW τ) y) ξ) +
       (diagVal (vertForm (Hω τ) π (eω τ) (lω τ) y) ξ + diagVal (horizForm (Hω τ) π (eω τ) (lω τ) y) ξ)) := by
    intro ξ; rw [key]; simp only [diagVal, mul_add, Finset.mul_sum, Complex.add_re, Complex.re_sum]
  have hJ := fun τ (h : Antitone (lam τ)) ξ => GlobalTheory.T.hodge_frame_flag_curvature GlobalTheory.T.subquotient_curvature_statement E ι (p τ) (q τ) U (ψ τ) (a τ) (b τ) Y π
    (AW τ) (eW τ) (Aω τ) (eω τ) (hψ τ) (ha τ) (hb τ) (hAW τ) (hAω τ) (heW τ) (heω τ) y hy (lam τ) h ξ
  have antW : ∀ τ, Antitone (lam τ) → Antitone (lW τ) := fun τ h i j hij =>
    h (by rw [Fin.le_def, Fin.coe_castAdd, Fin.coe_castAdd]; exact hij)
  have antω : ∀ τ, Antitone (lam τ) → Antitone (lω τ) := fun τ h i j hij =>
    h (by rw [Fin.le_def, Fin.coe_natAdd, Fin.coe_natAdd]; exact Nat.add_le_add_left hij _)
  have hnn : ∀ τ, Antitone (lam τ) → ∀ ξ,
      0 ≤ (diagVal (vertForm (HW τ) π (eW τ) (lW τ) y) ξ + diagVal (horizForm (HW τ) π (eW τ) (lW τ) y) ξ) +
       (diagVal (vertForm (Hω τ) π (eω τ) (lω τ) y) ξ + diagVal (horizForm (Hω τ) π (eω τ) (lω τ) y) ξ) := by
    intro τ h ξ
    have h1 := vertForm_nonneg (HW τ) π (eW τ) (antW τ h) y ξ
    have h2 := vertForm_nonneg (Hω τ) π (eω τ) (antω τ h) y ξ
    have h3 := (hJ τ h ξ).1
    rw [diagVal_zero] at h1 h2
    linarith
  refine ⟨fun hanti ξ => ?_, fun hstrict hsec hflag ξ hξ => ?_⟩
  · rw [diagVal_zero, hsum]
    exact Finset.sum_nonneg fun τ _ => hnn τ (hanti τ) ξ
  · rw [hsum]
    have hanti : ∀ τ, Antitone (lam τ) := fun τ => (hstrict τ).antitone
    refine Finset.sum_pos' (fun τ _ => hnn τ (hanti τ) ξ) ?_
    by_cases hv : fderiv ℂ π y ξ = 0
    · have : ¬ ((∀ τ, FixesFlag (AW τ) y ξ) ∧ ∀ τ, FixesFlag (Aω τ) y ξ) :=
        fun h => hξ (hflag ξ hv h.1 h.2)
      rw [not_and_or] at this
      rcases this with h | h
      · push_neg at h
        obtain ⟨τ, hτ⟩ := h
        have hne : ∃ i l, i < l ∧ thetaOneZero (HW τ) π (eW τ) y ξ l i ≠ 0 := by
          by_contra hc; push_neg at hc
          exact hτ (GlobalTheory.T.theta_vanish_on_fiber_tangent E ι (p τ) U (HW τ) Y π (AW τ) (eW τ) (hP τ).1 (hAW τ) (heW τ) y hy ξ hv hc)
        have hsW : StrictAnti (lW τ) := fun i j hij => hstrict τ (by rw [Fin.lt_def, Fin.coe_castAdd, Fin.coe_castAdd]; exact hij)
        have h1 := vertForm_pos (HW τ) π (eW τ) hsW y ξ hne
        have h2 := vertForm_nonneg (Hω τ) π (eω τ) (antω τ (hanti τ)) y ξ
        have h3 := (hJ τ (hanti τ) ξ).1
        rw [diagVal_zero] at h2
        exact ⟨τ, Finset.mem_univ _, by linarith⟩
      · push_neg at h
        obtain ⟨τ, hτ⟩ := h
        have hne : ∃ i l, i < l ∧ thetaOneZero (Hω τ) π (eω τ) y ξ l i ≠ 0 := by
          by_contra hc; push_neg at hc
          exact hτ (GlobalTheory.T.theta_vanish_on_fiber_tangent E ι (q τ) U (Hω τ) Y π (Aω τ) (eω τ) (hP τ).2 (hAω τ) (heω τ) y hy ξ hv hc)
        have hsω : StrictAnti (lω τ) := fun i j hij => hstrict τ (by rw [Fin.lt_def, Fin.coe_natAdd, Fin.coe_natAdd]; exact Nat.add_lt_add_left hij _)
        have h1 := vertForm_pos (Hω τ) π (eω τ) hsω y ξ hne
        have h2 := vertForm_nonneg (HW τ) π (eW τ) (antW τ (hanti τ)) y ξ
        have h3 := (hJ τ (hanti τ) ξ).1
        rw [diagVal_zero] at h2
        exact ⟨τ, Finset.mem_univ _, by linarith⟩
    · have : ¬ ∀ τ, secondForm (ψ τ) (π y) (fderiv ℂ π y ξ) = 0 := fun h => hv (hsec _ h)
      push_neg at this
      obtain ⟨τ, hτ⟩ := this
      have h1 := (hJ τ (hanti τ) ξ).2 (hstrict τ) hτ
      have h2 := vertForm_nonneg (HW τ) π (eW τ) (antW τ (hanti τ)) y ξ
      have h3 := vertForm_nonneg (Hω τ) π (eω τ) (antω τ (hanti τ)) y ξ
      rw [diagVal_zero] at h2 h3
      exact ⟨τ, Finset.mem_univ _, by linarith⟩

theorem statement : GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.Statement := ⟨glc, clb, hp⟩

end GlobalTheory.GradedLines

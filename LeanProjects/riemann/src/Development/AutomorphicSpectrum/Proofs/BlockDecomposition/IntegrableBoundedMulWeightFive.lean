import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.GammaSplitting.UnipotentTateFunctionalEquation

open MeasureTheory Matrix Filter Topology
open Ad3 Ad3.K Ad3.K.LC Ad3.K.LC.C

noncomputable section

namespace GlobalTheory.CompanionTheory.ParsC

abbrev V2 : Type := Fin 2 → ℂ

def mv (κ : M22) (z : V2) : V2 := (Matrix.of κ).mulVec z

def col (κ : M22) (y : V2) : M23 := ![![κ 0 0, κ 0 1, y 0], ![κ 1 0, κ 1 1, y 1]]

def ip (κ : M22) : ℂ := κ 0 0 * (starRingEnd ℂ) (κ 0 1) + κ 1 0 * (starRingEnd ℂ) (κ 1 1)

def nr (κ : M22) : ℝ := ‖κ 0 1‖ ^ 2 + ‖κ 1 1‖ ^ 2

def D0 (κ : M22) : ℝ := (max (‖(Matrix.of κ).det‖ ^ 2) (‖ip κ‖ ^ 2 / nr κ))⁻¹

def w5 (y : V2) : ℝ := ((1 + ‖y‖) ^ 5)⁻¹

def gw (ε : ℝ) (v w : ℂ) : ℝ := Ad3.K.LC.C.ge ε (w - v)

def G1 (ε : ℝ) (v c w : ℂ) : ℝ := -2 * Real.pi * ε ^ 2 * (((starRingEnd ℂ) c * (w - v)).re) * gw ε v w

def G2 (ε : ℝ) (v c w : ℂ) : ℝ :=
  (-2 * Real.pi * ε ^ 2 * ‖c‖ ^ 2 + 4 * Real.pi ^ 2 * ε ^ 4 * (((starRingEnd ℂ) c * (w - v)).re) ^ 2) * gw ε v w

section
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def dq (Ψ : SchwartzMap (M23 × V2) F) : SchwartzMap (M23 × V2) (V2 →L[ℝ] F) :=
  SchwartzMap.postcompCLM (𝕜 := ℝ)
    ((ContinuousLinearMap.compL ℝ V2 (M23 × V2) F).flip (ContinuousLinearMap.inr ℝ M23 V2))
    (SchwartzMap.fderivCLM ℝ (M23 × V2) F Ψ)

def AF (Ψ : SchwartzMap (M23 × V2) F) (ε : ℝ) (κ : M22) (v : ℂ) (q : V2) : F :=
  ∫ z : V2, (psiC (-(z 1)) * (gw ε v (z 0) : ℂ)) • Ψ (col κ (mv κ z), q)

end

lemma Dk_eq (N : ℕ) (κ : M22) : Dk N κ = D0 κ / (1 + ‖κ‖) ^ N := rfl

lemma col_mv (κ : M22) (z : V2) : Matrix.of.symm (Matrix.of κ * blk z) = col κ (mv κ z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [col, mv, blk, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma Aq_eq (Ψ : Sw) (ε : ℝ) (κ : M22) (v : ℂ) (q : V2) : Aq Ψ ε κ v q = AF Ψ ε κ v q := by
  unfold Aq AF gw
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [col_mv, smul_eq_mul]
  ring

theorem cov : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : M22), (Matrix.of κ).det ≠ 0 → ∀ φ : V2 → E,
    (∫ z, φ (mv κ z)) = ((‖(Matrix.of κ).det‖ ^ 2)⁻¹ : ℝ) • (∫ y, φ y) ∧ (Integrable φ → Integrable (fun z => φ (mv κ z))) := by
  intro E _ _ κ h φ
  set D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of κ with hD
  set f : V2 →ₗ[ℝ] V2 := (Matrix.toLin' D).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = Complex.normSq D.det := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  have hpos : 0 < Complex.normSq D.det := Complex.normSq_pos.2 h
  have hne : LinearMap.det f ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure V2)) hne
  have hme : MeasurableEmbedding f :=
    ((LinearMap.equivOfDetNeZero f hne).toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
  have hmv : ∀ z, mv κ z = f z := fun z => rfl
  have hn : Complex.normSq D.det = ‖D.det‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hfin : ENNReal.ofReal |(LinearMap.det f)⁻¹| ≠ ⊤ := ENNReal.ofReal_ne_top
  constructor
  · have e1 : ∫ z, φ (mv κ z) = ∫ y, φ y ∂(Measure.map f volume) := by
      rw [hme.integral_map]; rfl
    rw [e1, hmap, integral_smul_measure, hdet, abs_inv, abs_of_pos hpos,
      ENNReal.toReal_ofReal (by positivity), hn]
  · intro hφ
    have e2 : Integrable φ (Measure.map f volume) := by
      rw [hmap]; exact hφ.smul_measure hfin
    exact (hme.integrable_map_iff.1 e2)

theorem int5 : Integrable w5 := by
  have hr : ((Module.finrank ℝ V2 : ℕ) : ℝ) < (5 : ℝ) := by
    have : Module.finrank ℝ V2 = 4 := by
      simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    rw [this]; norm_num
  have := integrable_one_add_norm (E := V2) (μ := volume) hr
  refine this.congr (Eventually.of_forall fun y => ?_)
  have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
  show (1 + ‖y‖) ^ (-(5 : ℝ)) = ((1 + ‖y‖) ^ 5)⁻¹
  rw [Real.rpow_neg hp.le]
  norm_cast

lemma norm_psiC (x : ℂ) : ‖psiC x‖ = 1 := by
  unfold psiC
  have : (-2 * Real.pi * Complex.I * (2 * x.re) : ℂ) = ((-2 * Real.pi * (2 * x.re) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma weightFive_nonneg (y : V2) : 0 ≤ w5 y := by unfold w5; positivity

lemma determinantWeight_nonneg (κ : M22) : 0 ≤ D0 κ := by
  unfold D0
  exact inv_nonneg.2 (le_max_of_le_left (by positivity))

lemma Dk_nonneg (N : ℕ) (κ : M22) : 0 ≤ Dk N κ := by
  rw [Dk_eq]; exact div_nonneg (determinantWeight_nonneg κ) (by positivity)

lemma int_w5mv (κ : M22) (h : (Matrix.of κ).det ≠ 0) : Integrable (fun z : V2 => w5 (mv κ z)) :=
  (cov ℝ κ h w5).2 int5

lemma integral_w5mv (κ : M22) (h : (Matrix.of κ).det ≠ 0) :
    ∫ z : V2, w5 (mv κ z) = (‖(Matrix.of κ).det‖ ^ 2)⁻¹ * ∫ y, w5 y := by
  simpa using (cov ℝ κ h w5).1

lemma integrable_bounded_mul_weightFive (κ : M22) (h : (Matrix.of κ).det ≠ 0) (W : ℂ → ℝ) (hW : Continuous W) (B : ℝ) (hB : ∀ w, |W w| ≤ B) :
    Integrable (fun z : V2 => W (z 0) * w5 (mv κ z)) := by
  refine (int_w5mv κ h).bdd_mul (c := B) (hW.comp (continuous_apply 0)).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  simpa using hB (z 0)

lemma nr_pos (κ : M22) (h : (Matrix.of κ).det ≠ 0) : 0 < nr κ := by
  unfold nr
  by_contra hn
  have h0 : ‖κ 0 1‖ ^ 2 + ‖κ 1 1‖ ^ 2 = 0 := le_antisymm (not_lt.1 hn) (by positivity)
  have h1 : κ 0 1 = 0 := by
    have : ‖κ 0 1‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖κ 1 1‖]) (by positivity)
    simpa using this
  have h2 : κ 1 1 = 0 := by
    have : ‖κ 1 1‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖κ 0 1‖]) (by positivity)
    simpa using this
  exact h (by simp [Matrix.det_fin_two, h1, h2])

end GlobalTheory.CompanionTheory.ParsC

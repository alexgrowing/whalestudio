import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset

noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.KHerm

variable {n : ℕ}

def skA (a b : Fin n) : Mat n := (1 / 2 : ℝ) • (Matrix.single a b (1 : ℂ) - Matrix.single b a (1 : ℂ))

def skB (a b : Fin n) : Mat n := (1 / 2 : ℝ) • (Matrix.single a b Complex.I + Matrix.single b a Complex.I)

theorem skA_skew (a b : Fin n) : (skA a b)ᴴ = -skA a b := by
  ext i j
  simp only [skA, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;> by_cases h4 : b = j <;> simp_all

theorem skB_skew (a b : Fin n) : (skB a b)ᴴ = -skB a b := by
  ext i j
  simp only [skB, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.single_apply]
  by_cases h1 : a = j <;> by_cases h2 : b = i <;> by_cases h3 : a = i <;> by_cases h4 : b = j <;> simp_all

theorem Kf_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf a b h).1 g = Rd (skA a b) h.1 g - Complex.I * Rd (skB a b) h.1 g := by
  have h1 : (Kf a b h).1 g = (e1 DR a b h).1 g - (f1 DR b a h).1 g := by
    simp [Kf, e2, sub_eq_add_neg]
  rw [h1, orderedCechToCatCochainsOne_apply_valueAtSubset a b h hg, liftOneFormsToCompatible_apply b a h hg]
  simp only [Eu, Rd, skA, skB, Pi.smul_apply, Pi.add_apply, if_true, Bool.false_eq_true, if_false,
    Matrix.mul_smul, mul_sub, mul_add, map_smul, map_sub, map_add, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem Rd_neg (X : Mat n) (f : Mat n → ℂ) (g : Mat n) : Rd (-X) f g = -Rd X f g := by
  simp [Rd]

theorem Kf_apply_swap (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (Kf b a h).1 g = -Rd (skA a b) h.1 g - Complex.I * Rd (skB a b) h.1 g := by
  have hA : skA b a = -skA a b := by
    simp only [skA, ← smul_neg, neg_sub]
  have hB : skB b a = skB a b := by
    simp only [skB, add_comm]
  rw [Kf_apply b a h hg, hA, hB, Rd_neg]

theorem Rd_conj_mul (X : Mat n) {x y : Mat n → ℂ} (hx : ContDiffOn ℝ ∞ x (GLs n)) (hy : ContDiffOn ℝ ∞ y (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (fun g => conj (x g) * y g) g = conj (Rd X x g) * y g + conj (x g) * Rd X y g := by
  have dx := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hx hg).hasFDerivAt
  have dy := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hy hg).hasFDerivAt
  have dc : HasFDerivAt (fun g => conj (x g)) (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ x g)) g :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp g dx
  have hm : HasFDerivAt (fun g => conj (x g) * y g) _ g := dc.mul dy
  simp only [Rd]
  rw [hm.fderiv]
  change conj (x g) * fderiv ℝ y g (g * X) + y g * conj (fderiv ℝ x g (g * X)) = _
  ring

theorem conj_mul_smooth {x y : Mat n → ℂ} (hx : ContDiffOn ℝ ∞ x (GLs n)) (hy : ContDiffOn ℝ ∞ y (GLs n)) :
    ContDiffOn ℝ ∞ (fun g => conj (x g) * y g) (GLs n) :=
  (Complex.conjCLE.toContinuousLinearMap.contDiff.comp_contDiffOn hx).mul hy

section Int

variable [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

omit [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] in
theorem cont_on_unit {f : Mat n → ℂ} (hf : ContinuousOn f (GLs n)) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => f k.1 :=
  hf.comp_continuous continuous_subtype_val fun k => unit_mem k

theorem integrable_of_cont {f : Matrix.unitaryGroup (Fin n) ℂ → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

end Int

end GlobalTheory.CompanionTheory.ModelS.KHerm

open GlobalTheory.CompanionTheory.ModelS.KHerm in

theorem GlobalTheory.CompanionTheory.ModelS.ipK_Kf_transpose : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ], (∀ u : Mat n → ℂ, ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0) → ∀ (a b : Fin n) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (GlobalTheory.CompanionTheory.ModelS.Kf a b x) y = GlobalTheory.CompanionTheory.ModelS.ipK κ x (GlobalTheory.CompanionTheory.ModelS.Kf b a y) := by
  intro n _ _ κ _ hI a b x y
  have hx := x.2.1
  have hy := y.2.1
  have i1 : ∀ X : Mat n, Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (Rd X x.1 k.1) * y.1 k.1) κ :=
    fun X => integrable_of_cont κ ((Complex.continuous_conj.comp
      (cont_on_unit (GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hx).continuousOn)).mul (cont_on_unit hy.continuousOn))
  have i2 : ∀ X : Mat n, Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * Rd X y.1 k.1) κ :=
    fun X => integrable_of_cont κ ((Complex.continuous_conj.comp (cont_on_unit hx.continuousOn)).mul
      (cont_on_unit (GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hy).continuousOn))
  have key : ∀ X : Mat n, Xᴴ = -X → (∫ k, conj (Rd X x.1 k.1) * y.1 k.1 ∂κ) + ∫ k, conj (x.1 k.1) * Rd X y.1 k.1 ∂κ = 0 := by
    intro X hX
    rw [← integral_add (i1 X) (i2 X), ← hI _ (conj_mul_smooth hx hy) X hX]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => (Rd_conj_mul X hx hy (unit_mem k)).symm)
  have L : ipK κ (Kf a b x) y = (∫ k, conj (Rd (skA a b) x.1 k.1) * y.1 k.1 ∂κ) +
      Complex.I * ∫ k, conj (Rd (skB a b) x.1 k.1) * y.1 k.1 ∂κ := by
    rw [← integral_const_mul, ← integral_add (i1 _) ((i1 _).const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Kf_apply a b x (unit_mem k), map_sub, map_mul, Complex.conj_I]
    ring
  have R : ipK κ x (Kf b a y) = -((∫ k, conj (x.1 k.1) * Rd (skA a b) y.1 k.1 ∂κ) +
      Complex.I * ∫ k, conj (x.1 k.1) * Rd (skB a b) y.1 k.1 ∂κ) := by
    rw [← integral_const_mul, ← integral_add (i2 _) ((i2 _).const_mul _), ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Kf_apply_swap a b y (unit_mem k)]
    ring
  rw [L, R]
  linear_combination key _ (skA_skew a b) + Complex.I * key _ (skB_skew a b)

import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarBox
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormMod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResCharIff

noncomputable section

open MeasureTheory Measure ValuativeRel Topology Module
open scoped NNReal ENNReal Pointwise

namespace PI.ProdFormulaE.HaarBox

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem modF_nonneg' (a : K) : 0 ≤ modF K a := by
  rcases eq_or_ne a 0 with h | h
  · rw [h, modF_zero]
  · exact (modF_pos h).le

variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def equivOfDet (b : Basis ι K E) (A : Matrix ι ι K) (hA : A.det ≠ 0) : E ≃ₗ[K] E :=
  LinearEquiv.ofIsUnitDet (f := Matrix.toLin b b A) (v := b) (v' := b)
    (by rw [LinearMap.toMatrix_toLin]; exact hA.isUnit)

theorem coe_equivOfDet (b : Basis ι K E) (A : Matrix ι ι K) (hA : A.det ≠ 0) :
    ⇑(equivOfDet b A hA) = Matrix.toLin b b A := rfl

variable [MeasurableSpace E] [BorelSpace E]

def ScaleBox (b : Basis ι K E) (μ : Measure E) : Prop :=
  ∀ (i : ι) (a : K) (ha : a ≠ 0),
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' box b 1) =
      (distribHaarChar K (Units.mk0 a ha) : ℝ≥0∞) * μ (box b 1)

def TransvBox (b : Basis ι K E) : Prop :=
  ∀ t : Matrix.TransvectionStruct ι K, ∃ γ : ι → ValueGroupWithZero K, (∀ i, γ i ≠ 0) ∧
    Matrix.toLin b b t.toMatrix '' box b γ = box b γ

private theorem measure_toLin_mul_image_of_forall (b : Basis ι K E) (μ : Measure E) (A B : Matrix ι ι K)
    (hA : ∀ S : Set E, μ (Matrix.toLin b b A '' S) = ENNReal.ofReal (modF K A.det) * μ S)
    (hB : ∀ S : Set E, μ (Matrix.toLin b b B '' S) = ENNReal.ofReal (modF K B.det) * μ S)
    (S : Set E) :
    μ (Matrix.toLin b b (A * B) '' S) = ENNReal.ofReal (modF K (A * B).det) * μ S := by
  rw [Matrix.toLin_mul b b b, LinearMap.coe_comp, Set.image_comp, hA, hB, Matrix.det_mul, modF_mul,
    ENNReal.ofReal_mul (modF_nonneg' _), mul_assoc]

private theorem measure_toLin_transvection_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (htrans : TransvBox b) (t : Matrix.TransvectionStruct ι K) (S : Set E) :
    μ (Matrix.toLin b b t.toMatrix '' S) = ENNReal.ofReal (modF K t.toMatrix.det) * μ S := by
  obtain ⟨γ, hγ, himg⟩ := htrans t
  have hdet : t.toMatrix.det ≠ 0 := by rw [Matrix.TransvectionStruct.det]; exact one_ne_zero
  rw [Matrix.TransvectionStruct.det, modF_one, ENNReal.ofReal_one, one_mul]
  have h := image_eq_of_box b μ (equivOfDet b t.toMatrix hdet) γ hγ 1
    (by rw [coe_equivOfDet, himg, one_mul]) S
  rwa [coe_equivOfDet, one_mul] at h

private theorem measure_toLin_diagonal_update_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (i : ι) (a : K) (ha : a ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' S) =
      ENNReal.ofReal (modF K (Matrix.diagonal (Function.update (1 : ι → K) i a)).det) * μ S := by
  have hdetv : (Matrix.diagonal (Function.update (1 : ι → K) i a)).det = a := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hdet : (Matrix.diagonal (Function.update (1 : ι → K) i a)).det ≠ 0 := by
    rw [hdetv]
    exact ha
  rw [hdetv, modF_of_ne ha, ENNReal.ofReal_coe_nnreal]
  have h := image_eq_of_box b μ (equivOfDet b _ hdet) 1 (fun _ => by simp) _
    (by rw [coe_equivOfDet]; exact hscale i a ha) S
  rwa [coe_equivOfDet] at h

private theorem measure_toLin_diagonal_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (D : ι → K) (hD : ∀ i, D i ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b (Matrix.diagonal D) '' S) =
      ENNReal.ofReal (modF K (Matrix.diagonal D).det) * μ S := by
  classical
  suffices h : ∀ s : Finset ι, ∀ D : ι → K, (∀ i, D i ≠ 0) → (∀ i ∉ s, D i = 1) → ∀ S : Set E,
      μ (Matrix.toLin b b (Matrix.diagonal D) '' S) =
        ENNReal.ofReal (modF K (Matrix.diagonal D).det) * μ S from
    h Finset.univ D hD (fun i hi => absurd (Finset.mem_univ i) hi) S
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro D _ h1 S
    have hD1 : D = 1 := funext fun i => h1 i (by simp)
    subst hD1
    have h1' : Matrix.diagonal (1 : ι → K) = 1 := Matrix.diagonal_one
    rw [h1', Matrix.toLin_one, LinearMap.id_coe, Set.image_id, Matrix.det_one, modF_one,
      ENNReal.ofReal_one, one_mul]
  | insert j s hj ih =>
    intro D h0 h1 S
    have hsplit : Matrix.diagonal D = Matrix.diagonal (Function.update D j 1) *
        Matrix.diagonal (Function.update 1 j (D j)) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]
    rw [hsplit]
    refine measure_toLin_mul_image_of_forall b μ _ _ (ih _ ?_ ?_) (measure_toLin_diagonal_update_image b μ hscale j (D j) (h0 j)) S
    · intro i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h, h0 i]
    · intro i hi
      by_cases h : i = j
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact h1 i (by simp [h, hi])

theorem image_toLin (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (htrans : TransvBox b)
    (A : Matrix ι ι K) (hA : A.det ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b A '' S) = ENNReal.ofReal (modF K A.det) * μ S := by
  classical
  revert S
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ S : Set E, μ (Matrix.toLin b b M '' S) = ENNReal.ofReal (modF K M.det) * μ S)
    A hA ?_ ?_ ?_
  · intro D hD S
    refine measure_toLin_diagonal_image b μ hscale D (fun i => ?_) S
    rw [Matrix.det_diagonal] at hD
    exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
  · intro t S
    exact measure_toLin_transvection_image b μ htrans t S
  · intro A B _ _ hA hB S
    exact measure_toLin_mul_image_of_forall b μ A B hA hB S

end PI.ProdFormulaE.HaarBox

namespace PI.ProdFormulaE.HaarAlgP

open HaarBox

theorem haarAlg_of
    (hscale : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (E : Type) [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsModuleTopology K E] [MeasurableSpace E] [BorelSpace E] (n : ℕ) (b : Basis (Fin n) K E)
      (μ : Measure E) [μ.IsAddHaarMeasure], ScaleBox b μ)
    (htrans : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (E : Type) [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsModuleTopology K E] (n : ℕ) (b : Basis (Fin n) K E), TransvBox b) :
    St.HaarAlg := by
  intro K _ _ _ _ A _ _ _ _ _ _ _ _ μ _ y hy S
  classical
  let b := Module.finBasis K A
  set M := LinearMap.toMatrix b b (LinearMap.mulLeft K y) with hM
  have hdet : M.det = Algebra.norm K y := by
    rw [hM, LinearMap.det_toMatrix, Algebra.norm_apply]
    rfl
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact (hy.map (Algebra.norm K)).ne_zero
  have h := image_toLin b μ (hscale K A _ b μ) (htrans K A _ b) M hdet0 S
  rw [hdet, hM, Matrix.toLin_toMatrix] at h
  exact h

end PI.ProdFormulaE.HaarAlgP

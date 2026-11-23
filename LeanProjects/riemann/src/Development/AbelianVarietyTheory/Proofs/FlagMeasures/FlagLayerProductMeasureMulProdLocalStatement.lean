import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLayerProductMeasureMulProdLocal
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagLayerProductMeasure_mul_prod_local : ∀ (ι : Type) [Fintype ι] (n f a : ℕ) (j : Fin a → ℕ) (s s₁ : Fin a → ℝ) (loc : ι → Fin a → ℝ), (∀ i, s i ^ f = s₁ i ^ f * ∏ v, loc v i) → layerProd n f j s id = layerProd n f j s₁ id * ∏ v, layerProd n 1 j (loc v) id := by
  first | exact @GlobalTheory.FlagMeas.layerProd_mul_prod | exact GlobalTheory.FlagMeas.layerProd_mul_prod | (intros; apply GlobalTheory.FlagMeas.layerProd_mul_prod <;> assumption)

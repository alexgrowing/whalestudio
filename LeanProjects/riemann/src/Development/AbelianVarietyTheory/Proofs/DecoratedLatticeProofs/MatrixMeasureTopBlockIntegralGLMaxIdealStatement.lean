import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixMeasureTopBlockIntegralGLMaxIdeal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
open MeasureTheory Matrix Formalism.IndefR.Datum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixMeasure_topBlock_integralGL_maxIdeal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (a b r : ℕ), r ≤ a → r ≤ b → (GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {x | topL r x ∈ Units.val '' (GlobalTheory.SplitWeil.KO k (Fin r) : Set (GL (Fin r) k)) ∧ (∀ i j, ValuativeRel.valuation k (x i j) ≤ 1) ∧ ∀ i j, r ≤ i.val → j.val < r → ValuativeRel.valuation k (x i j) < 1}).toReal = (GlobalTheory.SplitWeil.volM ν (Fin b) (Fin a) {x | ∀ i j, ValuativeRel.valuation k (x i j) ≤ 1}).toReal * ((∏ n ∈ Finset.Ioc 0 r, (1 - ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ n)⁻¹)) * ((GlobalTheory.SplitWeil.resCard k : ℝ) ^ (r * (b - r)))⁻¹) := by
  first | exact @GlobalTheory.RectBlockVolume.vol_topBlock_KO | exact GlobalTheory.RectBlockVolume.vol_topBlock_KO | (intros; apply GlobalTheory.RectBlockVolume.vol_topBlock_KO <;> assumption)

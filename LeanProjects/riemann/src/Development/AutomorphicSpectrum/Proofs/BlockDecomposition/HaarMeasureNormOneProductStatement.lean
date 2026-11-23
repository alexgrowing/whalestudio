import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureNormOneProduct
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_measure_norm_one_product : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (GroundTheory.Automorphic.Reduction.normOneGL E a)) [ν.IsHaarMeasure], ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ Measure.map (fun p : GroundTheory.Automorphic.Reduction.normOneGL E a × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ := by
  first | exact @GlobalTheory.CompanionTheory.HaarSplit.map_prod_eq_smul | exact GlobalTheory.CompanionTheory.HaarSplit.map_prod_eq_smul | (intros; apply GlobalTheory.CompanionTheory.HaarSplit.map_prod_eq_smul <;> assumption)

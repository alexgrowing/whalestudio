import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereMeasureFinite
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_measure_finite : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (O : Set X), IsOpen O → (∀ (j : Fin A.n) (x : X), x ∈ (A.chart j).source → ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∫⁻ y in (A.chart j).target ∩ (A.chart j).symm ⁻¹' (V ∩ O), ENNReal.ofReal (locDens A Φ j y) < ⊤) → maMeasure A Φ O < ⊤ := by
  first | exact @GlobalTheory.maMeasure_lt_top_of_locally_finite | exact GlobalTheory.maMeasure_lt_top_of_locally_finite | (intros; apply GlobalTheory.maMeasure_lt_top_of_locally_finite <;> assumption)

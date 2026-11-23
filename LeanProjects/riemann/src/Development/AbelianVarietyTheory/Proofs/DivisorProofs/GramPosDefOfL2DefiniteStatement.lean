import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefOfL2Definite
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_posDef_of_l2_definite : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (∀ c : ι → ℂ, l2 μ v c = 0 → c = 0) → (gram μ v).PosDef := by
  first | exact @GlobalTheory.HSAmp.gram_posDef | exact GlobalTheory.HSAmp.gram_posDef | (intros; apply GlobalTheory.HSAmp.gram_posDef <;> assumption)

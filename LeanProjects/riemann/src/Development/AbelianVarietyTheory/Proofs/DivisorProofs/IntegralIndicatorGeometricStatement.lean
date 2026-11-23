import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralIndicatorGeometric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValAtOfUnder

noncomputable section

open scoped TensorProduct NNReal nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_indicator_geometric : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] {ι : Type} [Fintype ι] (o : G →* Multiplicative (ι → ℤ)), Function.Surjective o → MeasurableSet {g : G | o g = 1} → μ {g : G | o g = 1} = 1 → ∀ (a : ι → ℂ), (∀ i, a i ≠ 0) → (∀ i, ‖a i‖ < 1) → ∀ c : ι → ℤ, ∫ g, Set.indicator {g : G | ∀ i, c i ≤ Multiplicative.toAdd (o g) i} (fun g => ∏ i, a i ^ Multiplicative.toAdd (o g) i) g ∂μ = ∏ i, a i ^ c i / (1 - a i) := by
  first | exact @GlobalTheory.UnrTate.integral_indicator_shells_eq_prod | exact GlobalTheory.UnrTate.integral_indicator_shells_eq_prod | (intros; apply GlobalTheory.UnrTate.integral_indicator_shells_eq_prod <;> assumption)

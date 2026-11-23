import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantCharactersSeparate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_characters_separate : ∀ (Z : Type) [TopologicalSpace Z] (β : (Z → ℂ) → (Z → ℂ) → ℂ),
    (∀ f ∈ SB Z, ∀ f' ∈ SB Z, ∀ g ∈ SB Z, β (f + f') g = β f g + β f' g) → (∀ f ∈ SB Z, ∀ g ∈ SB Z, ∀ g' ∈ SB Z, β f (g + g') = β f g + β f g') →
    (∀ (a : ℂ), ∀ f ∈ SB Z, ∀ g ∈ SB Z, β (a • f) g = a * β f g ∧ β f (a • g) = starRingEnd ℂ a * β f g) →
    (∀ x y : Z, x ≠ y → ∃ χ : Z → ℂ, IsLocallyConstant χ ∧ (∀ z, ‖χ z‖ = 1) ∧ χ x ≠ χ y ∧ ∀ f ∈ SB Z, ∀ g ∈ SB Z, β (χ * f) (χ * g) = β f g) →
    ∀ f ∈ SB Z, ∀ g ∈ SB Z, (∀ x, f x * g x = 0) → β f g = 0 := by
  first | exact @GlobalTheory.SBOrth.sesq_eq_zero_of_mul_eq_zero | exact GlobalTheory.SBOrth.sesq_eq_zero_of_mul_eq_zero | (intros; apply GlobalTheory.SBOrth.sesq_eq_zero_of_mul_eq_zero <;> assumption)

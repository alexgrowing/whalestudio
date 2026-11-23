import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFunctionalUnique
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_statement_2 : ∀ {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (β : LinearMap.BilinForm ℝ Y),
    β.Nondegenerate → ∀ Λ : Submodule ℝ (Y × Y), (∀ l ∈ Λ, ∀ l' ∈ Λ, β l.1 l'.2 = β l'.1 l.2) →
    (∀ v : Y × Y, (∀ l ∈ Λ, β v.1 l.2 = β l.1 v.2) → v ∈ Λ) → ∀ ℓ ℓ' : SchwartzMap Y ℂ →L[ℂ] ℂ,
    (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → ℓ g = ℓ f) →
    (∀ l ∈ Λ, ∀ f g : SchwartzMap Y ℂ, ⇑g = sch β l.1 l.2 ⇑f → ℓ' g = ℓ' f) → ℓ ≠ 0 → ∃ c : ℂ, ℓ' = c • ℓ := by
  first | exact @GlobalTheory.ArchSch.LagUniq.lag_uniq | exact GlobalTheory.ArchSch.LagUniq.lag_uniq | (intros; apply GlobalTheory.ArchSch.LagUniq.lag_uniq <;> assumption)

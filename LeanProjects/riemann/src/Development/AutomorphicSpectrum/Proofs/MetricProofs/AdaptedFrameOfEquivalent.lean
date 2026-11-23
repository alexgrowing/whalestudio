import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

namespace LatEmb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem perExt_of_coord {R R' : RiemLat E g Λ} (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ x, R'.P x = k (R.P x))
    (y : Ψ → Fin (j + j') → ℂ) : C.perExt R' y = k (C.perExt R y) := by
  have h : C.perExt R' = (k.toLinearMap.restrictScalars ℝ) ∘ₗ C.perExt R := by
    refine C.bas.ext fun i => ?_
    simp [perExt, Module.Basis.constr_basis, hk]
  rw [h]
  rfl

theorem pPart_of_coord {R R' : RiemLat E g Λ} (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ x, R'.P x = k (R.P x))
    (τ : Ψ) (y : Fin (j + j') → ℂ) : C.pPart R' τ y = k (C.pPart R τ y) := by
  simp only [pPart, C.perExt_of_coord k hk, map_smul, map_sub]

theorem pBar_of_coord {R R' : RiemLat E g Λ} (k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hk : ∀ x, R'.P x = k (R.P x))
    (τ : Ψ) (y : Fin (j + j') → ℂ) : C.pBar R' τ y = k (C.pBar R τ y) := by
  simp only [pBar, C.perExt_of_coord k hk, map_smul, map_add]

end LatEmb

theorem isAdapted_of_eqvBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R R' : RiemLat E g Λ) (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted R A → R.EqvBy R' 1 → C.IsAdapted R' A := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C R R' A hA hE
  obtain ⟨k, hk⟩ := hE
  have hk' : ∀ x, R'.P x = k (R.P x) := fun x => hk x
  refine ⟨hA.unit, fun τ v => ?_, fun τ v => ?_⟩
  · rw [C.pPart_of_coord k hk', hA.ker, map_zero]
  · rw [C.pBar_of_coord k hk', hA.kerBar, map_zero]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherBis
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem ModelChangeNef.proof (hC : ModelCurves.Statement) (hN : ModelCurveNum.Statement) :
    ModelChangeNef.Statement := by
  have key : ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (N : ℕ)
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
      (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1)),
      IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀' →
      IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm →
      ∀ (β : K → ℤ) (β' : K' → ℤ),
        (∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
            secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) →
        IndefiniteRowSideFullHecke.Kleiman2.IsNef F y β → IndefiniteRowSideFullHecke.Kleiman2.IsNef F y' β' := by
    intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs hnef W' hW' hle' hrel'
    obtain ⟨hP, hPle, hPrel⟩ := (hC F K' ι' Ω y' k₀' N e' _ hx hm' 1).1 W' hW' hle' hrel'
    obtain ⟨W, hW, hle, hrel, hWP⟩ := (hC F K ι Ω y k₀ N e _ rfl hm 1).2 _ hP hPle hPrel
    rw [← hN F Ω N K ι y k₀ e K' ι' y' k₀' e' hm hm' hx β β' hs W W' hW hle hrel hW' hle' hrel' hWP]
    exact hnef W hW hle hrel
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hm hm' hx β β' hs
  exact ⟨key F Ω N K ι y k₀ e K' ι' y' k₀' e' hm hm' hx β β' hs,
    key F Ω N K' ι' y' k₀' e' K ι y k₀ e hm' hm hx.symm β' β fun c => (hs c).symm⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

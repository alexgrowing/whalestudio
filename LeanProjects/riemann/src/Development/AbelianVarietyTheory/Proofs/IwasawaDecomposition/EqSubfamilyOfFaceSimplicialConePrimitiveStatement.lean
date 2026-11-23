import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqSubfamilyOfFaceSimplicialConePrimitive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_subfamily_of_face_simplicialCone_primitive : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (hδ : ∀ i, δ i ∈ balForms bar X)
    (hγ : ∀ j, γ j ∈ balForms bar X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    LinearIndependent ℤ δ → LinearIndependent ℤ γ → (∀ i, IsPrim bar (⟨δ i, hδ i⟩ : balForms bar X)) →
    (∀ j, IsPrim bar (⟨γ j, hγ j⟩ : balForms bar X)) → (∀ j, InRCone δ (γ j)) → (∀ i, 0 ≤ h (δ i)) →
    (∀ j, h (γ j) = 0) → (∀ i, h (δ i) = 0 → InRCone γ (δ i)) →
    ∃ s : Fin n ↪ Fin m, (∀ j, γ j = δ (s j)) ∧ ∀ i, h (δ i) = 0 ↔ i ∈ Set.range s := by
  first | exact @GlobalTheory.PolFan.eq_subfamily_of_face | exact GlobalTheory.PolFan.eq_subfamily_of_face | (intros; apply GlobalTheory.PolFan.eq_subfamily_of_face <;> assumption)

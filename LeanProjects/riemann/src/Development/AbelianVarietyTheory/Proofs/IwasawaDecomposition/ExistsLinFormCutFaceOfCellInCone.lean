import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntLinearFormCuttingSubcell

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.CellFace

theorem exists_face_form : ∀ {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m n : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar ψ γ → IsCell bar ψ γ' → (∀ j, InRCone γ (γ' j)) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (γ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 → InRCone γ' β := by
  intro O _ bar ψ X _ _ _ m n γ γ' hγ hγ' hin
  exact exists_cut_of_cell_le O bar ψ X m n γ γ' hγ hγ' hin

end GlobalTheory.PolFan.CellFace

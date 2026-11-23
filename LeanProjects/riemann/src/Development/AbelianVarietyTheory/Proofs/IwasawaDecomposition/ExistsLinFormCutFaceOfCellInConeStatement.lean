import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLinFormCutFaceOfCellInCone
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone : ∀ {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m n : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar ψ γ → IsCell bar ψ γ' → (∀ j, InRCone γ (γ' j)) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (γ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 → InRCone γ' β := by
  first | exact @GlobalTheory.PolFan.CellFace.exists_face_form | exact GlobalTheory.PolFan.CellFace.exists_face_form | (intros; apply GlobalTheory.PolFan.CellFace.exists_face_form <;> assumption)

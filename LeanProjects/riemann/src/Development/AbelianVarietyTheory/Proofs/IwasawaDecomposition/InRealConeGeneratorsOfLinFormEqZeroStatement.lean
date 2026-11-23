import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeGeneratorsOfLinFormEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inRealCone_generators_of_linForm_eq_zero : ∀ {X : Type} [AddCommGroup X] {m p : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ)
    (e : Fin p ↪ Fin m) (β : LinearMap.BilinForm ℤ X), (∀ i, 0 ≤ h (δ i)) → (∀ i, h (δ i) = 0 → i ∈ Set.range e) →
    InRCone δ β → h β = 0 → InRCone (fun k => δ (e k)) β := by
  first | exact @GlobalTheory.PolFan.inRCone_of_apply_eq_zero | exact GlobalTheory.PolFan.inRCone_of_apply_eq_zero | (intros; apply GlobalTheory.PolFan.inRCone_of_apply_eq_zero <;> assumption)

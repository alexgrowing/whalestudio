import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellMultiplicityPositiveCone
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAdmissibleFanOfCellMultOneCMField
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_multiplicity_positive_cone : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m p : ℕ}
    (δ : Fin m → balForms bar X) (β : balForms bar X) (c : Fin m → ℝ) (j : Fin m) (e : Fin p ↪ Fin m),
    LinearIndependent ℤ δ → toReal (β : LinearMap.BilinForm ℤ X) = ∑ i, c i • toReal (δ i : LinearMap.BilinForm ℤ X) →
    0 < c j → (∀ i, i ∈ Set.range e ↔ i ≠ j) → 0 < cellMult bar δ →
    (cellMult bar (Fin.cons β (fun k => δ (e k)) : Fin (p + 1) → balForms bar X) : ℝ) = c j * cellMult bar δ := by
  first | exact @GlobalTheory.PolFan.ConsMult.cellMult_cons_eq | exact GlobalTheory.PolFan.ConsMult.cellMult_cons_eq | (intros; apply GlobalTheory.PolFan.ConsMult.cellMult_cons_eq <;> assumption)

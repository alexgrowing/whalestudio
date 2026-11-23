import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorsSmulMemOtherCellCone
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_generators_smul_mem_other_cellCone : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m m' : ℕ} (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin m' → LinearMap.BilinForm ℤ X)
    (c : Fin m' → ℝ), IsCell bar φ δ → IsCell bar φ γ → (∀ j, 0 ≤ c j) →
    ∑ i, toReal (δ i) = ∑ j, c j • toReal (γ j) →
    ∀ i, ∃ (k : ℕ) (a : Fin m' → ℕ), 0 < k ∧ k • δ i = ∑ j, a j • γ j := by
  first | exact @GlobalTheory.PolFan.exists_smul_eq_sum_of_sum_toReal_eq | exact GlobalTheory.PolFan.exists_smul_eq_sum_of_sum_toReal_eq | (intros; apply GlobalTheory.PolFan.exists_smul_eq_sum_of_sum_toReal_eq <;> assumption)

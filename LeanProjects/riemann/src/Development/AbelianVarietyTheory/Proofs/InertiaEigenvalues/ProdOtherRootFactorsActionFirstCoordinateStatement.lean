import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOtherRootFactorsActionFirstCoordinate
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_other_root_factors_action_first_coordinate : ∀ {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ} (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))) (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → (∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2)) → (∀ u, e ((X₀.map (toFr O)).mulVec u) = (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) → ∀ u, e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) = (0, fun c : Fin t => if (c : ℕ) = 0 then toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  first | exact @GlobalTheory.RootFactorProduct.prod_other_factors_action | exact GlobalTheory.RootFactorProduct.prod_other_factors_action | (intros; apply GlobalTheory.RootFactorProduct.prod_other_factors_action <;> assumption)

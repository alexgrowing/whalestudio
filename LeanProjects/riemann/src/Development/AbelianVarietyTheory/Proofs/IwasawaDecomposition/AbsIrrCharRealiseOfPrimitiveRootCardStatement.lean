import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharRealiseOfPrimitiveRootCard
import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgFin
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrChar_realise_of_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] (σ : K →+* ℂ) (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (ψ : G → ℂ), ψ ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ → ∃ χ : G → K, IsAbsIrrChar χ ∧ ∀ g, σ (χ g) = ψ g := by
  first | exact @GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | exact GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot | (intros; apply GlobalTheory.BrauerRealise.absIrr_realise_of_isPrimitiveRoot <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharMemClosurePrimitiveRootCard
import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgFin
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrChar_mem_closure_primitiveRoot_card : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] [inst_3 : CharZero K] (z : K), IsPrimitiveRoot z (Fintype.card G) → ∀ (χ : G → K), IsAbsIrrChar χ → ∀ g : G, χ g ∈ Subring.closure ({z} : Set K) := by
  first | exact @GlobalTheory.absIrrChar_mem_closure_primitiveRoot | exact GlobalTheory.absIrrChar_mem_closure_primitiveRoot | (intros; apply GlobalTheory.absIrrChar_mem_closure_primitiveRoot <;> assumption)

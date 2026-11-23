import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbsIrrCharCompMemComplexIrrCharSet
import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgFin
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrChar_comp_mem_complexIrrCharSet : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] {K : Type} [inst_2 : Field K] [inst_3 : CharZero K] (σ : K →+* ℂ) (χ : G → K), IsAbsIrrChar χ → (fun g => σ (χ g)) ∈ Formalism.L2.Col.gxIrrSet (G := G) ℂ := by
  first | exact @GlobalTheory.absIrrChar_comp_mem_gxIrrSet | exact GlobalTheory.absIrrChar_comp_mem_gxIrrSet | (intros; apply GlobalTheory.absIrrChar_comp_mem_gxIrrSet <;> assumption)

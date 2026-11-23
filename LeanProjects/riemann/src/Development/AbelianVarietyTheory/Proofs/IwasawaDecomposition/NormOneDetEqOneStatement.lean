import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneDetEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_one_det_eq_one : ∀ (F : Type) [Field F] (n c : ℕ), ∀ r ∈ Loc.N1 F n c, LinearEquiv.det r = 1 := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip | exact GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip | (intros; apply GlobalTheory.Mem.Col2.IdxEx.det_eq_one_of_mem_unip <;> assumption)

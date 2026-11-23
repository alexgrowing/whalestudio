import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusEigenFilEqQlMulTPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (r : ℕ) (x : Per.Acris l), phiA l x = (l : Per.Acris l) ^ r * x → C.j x ∈ Per.FilP l r → ∃ (z : ℤ_[l]) (k : ℕ), (l : Per.Acris l) ^ k * x = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z) * C.t ^ r := by
  first | exact @GlobalTheory.MemLoc.fix_pow | exact GlobalTheory.MemLoc.fix_pow | (intros; apply GlobalTheory.MemLoc.fix_pow <;> assumption)

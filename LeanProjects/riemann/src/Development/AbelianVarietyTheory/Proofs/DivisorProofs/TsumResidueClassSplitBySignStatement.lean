import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumResidueClassSplitBySign
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_residueClass_split_by_sign : ∀ (N : ℕ) [NeZero N] (r : ZMod N) (R : ℤ → ℂ), Summable (fun n : ℤ => R ((r.val : ℤ) + n * N)) → ∑' n : ℤ, R ((r.val : ℤ) + n * N) = (if r = 0 then R 0 else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = r then R ((d : ℕ) : ℤ) else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = -r then R (-((d : ℕ) : ℤ)) else 0) := by
  first | exact @GlobalTheory.WpFam.tsum_residue_class_split | exact GlobalTheory.WpFam.tsum_residue_class_split | (intros; apply GlobalTheory.WpFam.tsum_residue_class_split <;> assumption)

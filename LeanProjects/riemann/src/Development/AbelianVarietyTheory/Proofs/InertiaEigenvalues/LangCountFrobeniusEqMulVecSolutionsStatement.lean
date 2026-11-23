import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LangCountFrobeniusEqMulVecSolutions
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lang_count_frobenius_eq_mulVec_solutions : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → A.det ≠ 0 → (∀ x : m → F, (∀ i, x i ^ p ^ e = A.mulVec x i) → Integral x) ∧ Nat.card {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} = (p ^ e) ^ Fintype.card m := by
  first | exact @GlobalTheory.PMonE.langCount | exact GlobalTheory.PMonE.langCount | (intros; apply GlobalTheory.PMonE.langCount <;> assumption)

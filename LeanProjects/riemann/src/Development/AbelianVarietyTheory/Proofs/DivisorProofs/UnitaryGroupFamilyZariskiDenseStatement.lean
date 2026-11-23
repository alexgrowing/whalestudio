import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupFamilyZariskiDense
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGNeZero
open Classical MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_family_zariski_dense : ∀ {ι : Type} [Fintype ι] {a : ℕ} (Q : MvPolynomial (ι × Fin a × Fin a) ℂ), (∀ g : ι → Matrix.unitaryGroup (Fin a) ℂ, MvPolynomial.eval (fun v : ι × Fin a × Fin a => (g v.1 : Matrix (Fin a) (Fin a) ℂ) v.2.1 v.2.2) Q = 0) → Q = 0 := by
  first | exact @GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense | exact GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense | (intros; apply GlobalTheory.UnitaryZariskiDense.unitary_zariski_dense <;> assumption)

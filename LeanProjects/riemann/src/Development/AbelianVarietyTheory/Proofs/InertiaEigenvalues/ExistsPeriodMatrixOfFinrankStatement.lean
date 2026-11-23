import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPeriodMatrixOfFinrank
import Mathlib
open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodMatrix_of_finrank_alt : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [IsDomain B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n F), (∀ g, (A g).det ≠ 0) → (∀ g (c : E), act g (algebraMap E B c) = algebraMap E B c) → (∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : E, b' = algebraMap E B c * b) → (∀ b : B, b ≠ 0 → (∀ g, ∃ x : F, act g b = algebraMap F B x * b) → IsUnit b) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n → ∃ Q : GL n B, ∀ g, (A g).map (algebraMap F B) * (Q : Matrix n n B).map (act g) = Q := by
  first | exact @GlobalTheory.RegularRing.exists_periodMatrix_of_finrank | exact GlobalTheory.RegularRing.exists_periodMatrix_of_finrank | (intros; apply GlobalTheory.RegularRing.exists_periodMatrix_of_finrank <;> assumption)

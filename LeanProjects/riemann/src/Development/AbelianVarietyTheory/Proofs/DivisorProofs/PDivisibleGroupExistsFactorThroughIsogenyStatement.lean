import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupExistsFactorThroughIsogeny
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivisibleGroup_exists_factor_through_isogeny : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G Q H : PDivGroup p k) (m : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (f : G ⟶ H), q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → q' ≫ q = (p : ℤ_[p]) ^ m • 𝟙 Q → kerIdeal (f.app m) ≤ kerIdeal (q.app m) → ∃ g : Q ⟶ H, q ≫ g = f := by
  first | exact @GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le | exact GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le | (intros; apply GlobalTheory.Dieu.exists_comp_eq_of_kerIdeal_le <;> assumption)

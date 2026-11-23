import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnramifiedExponentOfIwahoriFixedVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelCasselmanHolds
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exponent_of_iwahori_fixed_vector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsAdmissible π → fixed π (iwahori k (Fin n)) ≠ ⊥ → ∃ χ : (Fin n → kˣ) →* ℂˣ, expMult π χ ≠ 0 := by
  first | exact @GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori | exact GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori | (intros; apply GlobalTheory.SmGL.exists_expMult_ne_zero_of_fixed_iwahori <;> assumption)

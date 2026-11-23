import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedElementLthPowerMod
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_element_lth_power_mod : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ a : fixA A, ∃ (b : fixA A) (z : A), (a : A) = (b : A) ^ l + (l : A) * z := by
  first | (exact @GlobalTheory.RecOne.fixA_eq_pow_add_mul) | (exact GlobalTheory.RecOne.fixA_eq_pow_add_mul) | (intros; apply GlobalTheory.RecOne.fixA_eq_pow_add_mul  <;> assumption)

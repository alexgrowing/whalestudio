import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLePowIffDvd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_pow_iff_dvd : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (n : ℕ) (x : c.O), ‖((x : c.O) : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ ↔ ((l : ℕ) : c.O) ^ n ∣ x := by
  first | exact @GlobalTheory.Coef.norm_le_norm_pow_iff_dvd | exact GlobalTheory.Coef.norm_le_norm_pow_iff_dvd | (intros; apply GlobalTheory.Coef.norm_le_norm_pow_iff_dvd <;> assumption)

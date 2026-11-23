import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterPowPredEqOneOfKillsPrimeRoots
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_pow_pred_eq_one_of_killsPrimeRoots : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l : ℕ) [Fact l.Prime] (C : Type) [Monoid C] (χ : G ℚ Ω →* C) (s : G ℚ Ω), KillsMu l χ → χ s ^ (l - 1) = 1 := by
  first | exact @GlobalTheory.KillsMuOrd.charPow_sub_one_eq_one | exact GlobalTheory.KillsMuOrd.charPow_sub_one_eq_one | (intros; apply GlobalTheory.KillsMuOrd.charPow_sub_one_eq_one <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormGaussSumModPrimePowerLeHalfPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_gaussSumModPrimePower_le_half_power : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), z ^ (l ^ m) = 1 → ‖gSum m z ψ‖ ≤ ‖(l : Qbar l) ^ (m / 2)‖ := by
  first | (exact @GlobalTheory.KZ.Cmp.norm_gSum_le) | (exact GlobalTheory.KZ.Cmp.norm_gSum_le) | (intros; apply GlobalTheory.KZ.Cmp.norm_gSum_le  <;> assumption)

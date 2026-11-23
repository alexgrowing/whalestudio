import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharUnramifiedInverseSplitPair
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_inverse_split_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar E) (v : HeightOneSpectrum (OF E)) (P P' : HeightOneSpectrum (𝓞 E)), TrivOnF χ → Splits v → Over P v → Over P' v → P ≠ P' → LevelLe χ P' 1 → UnrAt χ P → UnrAt χ P' ∧ val χ P' = (val χ P)⁻¹ := by
  first | exact @GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val | exact GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val | (intros; apply GlobalTheory.CMVal.Euler.SplitPair.unrAt_and_val <;> assumption)

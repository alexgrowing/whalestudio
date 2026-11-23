import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationResidueFiniteUnram
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_residue_finite_unram : ∀ (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).Finite ∧ ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).FormallyUnramified := by
  first | exact @GlobalTheory.residue_atMaximal_finite_formallyUnramified | exact GlobalTheory.residue_atMaximal_finite_formallyUnramified | (intros; apply GlobalTheory.residue_atMaximal_finite_formallyUnramified <;> assumption)

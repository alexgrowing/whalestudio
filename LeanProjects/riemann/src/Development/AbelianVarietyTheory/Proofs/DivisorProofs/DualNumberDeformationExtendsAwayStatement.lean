import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberDeformationExtendsAway
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualNumber_deformation_extend_away : ∀ {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] (g : S) [IsLocalization.Away g S'] (d : S →+* DualNumber S), (∀ s, (d s).fst = s) → ∃ d' : S' →+* DualNumber S', (∀ s, (d' s).fst = s) ∧ ∀ s, (d' (algebraMap S S' s)).snd = algebraMap S S' (d s).snd := by
  first | exact @GlobalTheory.dualNumber_deformation_extends_away | exact GlobalTheory.dualNumber_deformation_extends_away | (intros; apply GlobalTheory.dualNumber_deformation_extends_away <;> assumption)

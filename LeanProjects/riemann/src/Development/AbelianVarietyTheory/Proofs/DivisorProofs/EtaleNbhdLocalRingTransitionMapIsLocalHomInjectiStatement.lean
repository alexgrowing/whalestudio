import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingTransitionMapIsLocalHomInjecti
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective : ∀ (R : Type) [CommRing R] [IsLocalRing R] (i j : EtNbhd R) (h : i ≤ j), IsLocalHom (EtNbhd.trans h) ∧ Function.Injective (EtNbhd.trans h) := by
  first | exact @GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective | exact GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective | (intros; apply GlobalTheory.Henselisation.EtNbhd.trans_isLocalHom_injective <;> assumption)

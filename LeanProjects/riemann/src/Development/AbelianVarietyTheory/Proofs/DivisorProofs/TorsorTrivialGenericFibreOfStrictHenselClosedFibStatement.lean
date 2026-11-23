import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialGenericFibreOfStrictHenselClosedFib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsorTrivialGenericFibre_of_strictHenselClosedFibre : GlobalTheory.LocAcyc.KeyLocal → GlobalTheory.LocAcyc.KeyAll := by
  first | (exact @GlobalTheory.LocAcyc.keyAll_of_keyLocal) | (exact GlobalTheory.LocAcyc.keyAll_of_keyLocal) | (intros; apply GlobalTheory.LocAcyc.keyAll_of_keyLocal  <;> assumption)

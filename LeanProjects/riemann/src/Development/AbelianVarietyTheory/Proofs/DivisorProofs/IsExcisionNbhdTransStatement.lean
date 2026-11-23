import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isExcisionNbhd_trans' : ∀ (A A' A'' : Type) [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A' A''] [Algebra A A''] [IsScalarTower A A' A''] (h : A), IsExcisionNbhd A A' h → IsExcisionNbhd A' A'' (algebraMap A A' h) → IsExcisionNbhd A A'' h := by
  first | (exact @GlobalTheory.EtC.isExcisionNbhd_trans) | (exact GlobalTheory.EtC.isExcisionNbhd_trans) | (intros; apply GlobalTheory.EtC.isExcisionNbhd_trans  <;> assumption)

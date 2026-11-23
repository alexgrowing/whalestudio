import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetBaseChangeOfDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_base_change_of_deformation : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → JetBC := by
  first | exact @GlobalTheory.LatJet.jetBC_of_grothendieckDeformation_abelianDeRham | exact GlobalTheory.LatJet.jetBC_of_grothendieckDeformation_abelianDeRham | (intros; apply GlobalTheory.LatJet.jetBC_of_grothendieckDeformation_abelianDeRham <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafExtendScalarsZmodSectionLocallyTmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafExtendScalars_zmod_section_locally_tmul : ∀ (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) (M : Shv (ZMod Q)) (U : Scheme.{0}) (y : Sec ((extSh (ZMod.castHom hq (ZMod q))).obj M) U), Loc U fun V g => ∃ x : Sec M V, extSh.sec (ZMod.castHom hq (ZMod q)) M V x = Sec.res g y := by
  first | (exact @GlobalTheory.EtC.ExtOnto.ext_onto) | (exact GlobalTheory.EtC.ExtOnto.ext_onto) | (intros; apply GlobalTheory.EtC.ExtOnto.ext_onto  <;> assumption)

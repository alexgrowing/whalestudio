import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDetStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (π : D.naut.CG 1) (w : PlE D.host) (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (P.chr.e1 π).1 w ξ), P.T.e w (D.naut.locG π w) = _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  first | exact @_root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp | exact _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp | (intros; apply _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp <;> assumption)
end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentificationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChangeStatement

namespace GlobalTheory.Proof.GoodComponentRecursion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem goodPartRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.PtLocal D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.GoodPartRec D.nd D.naut i := by
  intro D hW h1 hlift hpt hbc hsp i
  exact GlobalTheory.Proof.SplitPlaceGoodSignature.goodPart_of_lifts D.nd D.naut i h1
    (GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification _ _ _ D.nd D.naut hW).1 (hlift i) (hpt i)
    (GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange _ _ _ D.nd D.naut i (hbc i) (hsp i))

end GlobalTheory.Proof.GoodComponentRecursion

import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameGeneratorResidual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownMemRecOfTies
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPartRecursion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharEtaBack
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParUpRecOfTies
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOneOfCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisBis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisTer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthogonalityOfFormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalPointThetaExhaustionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointOfPrvConditionsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsCClose

theorem main : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), Join P → GlobalTheory.NRows.RowsA D →
    GlobalTheory.NRows.RowsB D → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.adm8 D → Formalism.MainNotions.SumRepresentations.Conclusion1 D →
    (∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i) → GlobalTheory.NRows.RowsC D := by
  intro hL D P J hA hB a1 a8 p1 hi
  obtain ⟨p41, _, p42⟩ := p1
  obtain ⟨tl, lt, io, rb⟩ := GlobalTheory.TieLabAt.main hL D P
  have iface := GlobalTheory.AdmIface.main D
  have bc : ∀ i, BCEx D.nd D.naut i := iface.1 a1
  have lift : ∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i := iface.2.2.1 p42
  have isot : Rows.IsotInternal D.what₂ := iface.2.2.2.2.2.mp a8
  have rho : GlobalDatumResidualRepCondition D :=
    GlobalTheory.ParamRep.jointCond_rho D hA.tie0 hA.a2 hB.a4 hA.a5 p41 (GlobalTheory.GoodCuspPoint.main D tl)
      (GlobalTheory.XiOver.main D P.cf P.C P.tp P.chr P.val hA.tie0 hA.a2 hA.a5)
  have rp : RowRepAtG D :=
    GlobalTheory.RowRepOcc.rowRepAtG_of_rowPoint D hA.tie0 hA.a2 hA.a5 p42 rho hA.gsp (GlobalTheory.T.rowPoint_of_conditions hL D P p42 p41)
  exact
    { c4b := GlobalTheory.RowTie.tameGenerator_residual D rb io lt rp
      rho := rho
      dz := GlobalTheory.GoodDepthZero.main D hA.tie0 hB.a4 p41 hA.gsp
      parUp := GlobalTheory.RowTie.parUpRec_of_ties D P.T hB.thetaOne (fun i => (hi i).1) bc (fun i => (hi i).2.1)
        (fun i => (hi i).2.2)
      downMem := GlobalTheory.RowTie.downMemRec_of_ties D P.T hB.thetaOne isot
        (fun i => GlobalTheory.PartOrthPin.main hL D P i ⟨J.rowM i⟩) (fun i => GlobalTheory.T.type_orthogonality_of_form hL D P i (J.form i))
        (fun i => (hi i).1) bc (fun i => (hi i).2.1)
      goodPart := GlobalTheory.Proof.GoodComponentRecursion.goodPartRec_of_ties D P.T hB.thetaOne lift (fun i => GlobalTheory.T.local_point_theta_exhaustion hL D P i) bc
        (fun i => (hi i).2.1) }

end GlobalTheory.RowsCClose

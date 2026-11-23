import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceBoundTuple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
namespace GlobalTheory.BigOn.Exp.TupLe.Swap
end GlobalTheory.BigOn.Exp.TupLe.Swap
namespace GlobalTheory.BigOn.Exp.TupLe
open GlobalTheory.BigOn.Exp.TupLe.Swap in
theorem flatSt_holds_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.FlatCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm B ψ t hB hB0 hψ hQ hxi hid
  have hL : Links2 p := _root_.GlobalTheory.T.links2_of_single_index_twisted D L hT Gi Gl Kc Y cX ex Csz p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  exact flat_gen _ _ _ _ _ _ (R2 p) (F2 p) hC p.qGuard j t (GlobalTheory.StdFrame.vStd_of_orthonormal_span _ j (p.stdV j))
    B ψ hB hB0 hψ hQ hxi hid
end GlobalTheory.BigOn.Exp.TupLe
end
end

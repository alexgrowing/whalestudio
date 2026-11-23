import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSuccStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroPointMemDoubleCosetClassRepStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepPointMemDoubleCosetClassRepStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroKernelLatticeEqPointKernelLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepKernelLatticeEqPointKernelLatticeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleDetEqAdelicPointDetStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.joint_dict : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  intro j hj La hLa
  cases j with
  | zero =>
    have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La).1
    exact ⟨hp, GlobalTheory.T.stepZero_point_mem_doubleCoset_classRep t std J La hLa, GlobalTheory.T.stepZero_kernelLattice_eq_pointKernelLattice t std J La, GlobalTheory.T.lattice_tuple_det_eq_adelic_point_det t std J 0 hj La _ hp⟩
  | succ j =>
    have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).1
    exact ⟨hp, GlobalTheory.T.succStep_point_mem_doubleCoset_classRep t std J j hj La hLa, GlobalTheory.T.succStep_kernelLattice_eq_pointKernelLattice t std J j hj La hLa, GlobalTheory.T.lattice_tuple_det_eq_adelic_point_det t std J (j + 1) hj La _ hp⟩

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadInjStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerOfAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TraceOfAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.KerRatAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatIoAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadCmpAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeHasSmallGenerators
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadComparisonAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Links2OfRowsStatement

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.SerBase
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)
end Point
theorem baseGe_of_serBase_facts_flatKer_centLat (hI : _root_.GlobalTheory.BigOn.Exp.ReadInjAlt) (hG : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators) (h1 : _root_.GlobalTheory.BigOn.Exp.SerBase.KerOfAtAlt) (h2 : _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt') (h3 : _root_.GlobalTheory.BigOn.Exp.SerBase.KernelRationalAt) (h4 : _root_.GlobalTheory.BigOn.Exp.SerBase.LatticeInclusionAt)
    (h5 : _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt) (hF : FlatKer) (hC : CentLat) (hTr : TraceRat) (hO : OwnUnit) : _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ := by
  unfold _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ _root_.GlobalTheory.BigOn.Exp.CanonicalFits _root_.GlobalTheory.BigOn.Exp.ReadInjAlt _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators _root_.GlobalTheory.BigOn.Exp.SerBase.KerOfAtAlt _root_.GlobalTheory.BigOn.Exp.SerBase.TraceAt' _root_.GlobalTheory.BigOn.Exp.SerBase.KernelRationalAt _root_.GlobalTheory.BigOn.Exp.SerBase.LatticeInclusionAt _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt _root_.GlobalTheory.BigOn.Exp.TwistConditions _root_.GlobalTheory.BigOn.AtPtsAlt at *
  refine ((((((Formalism.MainNotions.Closed.and hI hG).and h1).and h2).and h3).and h4).and h5).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := H
  obtain ⟨x0, hx0⟩ := (((((a1.and a2).and a3).and a4).and a5).and a6).and a7
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν rd hfit hcan => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hx0 x hx hle i p hp
  exact baseLat_le_realBase p w j hfit (b1 hm w hw j ρ hρ ν hfit.norm.1) (b2 hm w hw j ρ hρ hfit.pin) fun h hh Q hQ g hg =>
    tmul_mem_realBase p w j (_root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hp hm.1) (b3 hm w hw j) (b4 hm w hw j) (b5 hm w hw j)
      (b6 hm w hw j) (b7 hm w hw j) hF hC hTr hO hfit hcan hh hQ hg
end GlobalTheory.BigOn.Exp.SerBase
namespace GlobalTheory.BigOn.Exp
theorem baseGe_of_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.BaseLowerBound₂ := fun hP hA hR hS =>
  _root_.GlobalTheory.BigOn.Exp.SerBase.baseGe_of_serBase_facts_flatKer_centLat _root_.GlobalTheory.T.read_injective _root_.GlobalTheory.T.latSmallGen' _root_.GlobalTheory.T.kerOfAt' _root_.GlobalTheory.T.trace_rationality_at_place' (_root_.GlobalTheory.T.kernel_rationality_of_reciprocity_hypotheses_alt hP hA hR hS) _root_.GlobalTheory.T.latIoAt' _root_.GlobalTheory.T.readCmpAt_of_serBase
    GlobalTheory.T.flatDatum_series_unit_times_kernel_series GlobalTheory.T.central_element_moves_coefficient_lattice_by_prime_pow GlobalTheory.T.kernelTrace_algebraic_at_lowestTypes GlobalTheory.T.ownPrime_isUnit_at_place
end GlobalTheory.BigOn.Exp
end
end

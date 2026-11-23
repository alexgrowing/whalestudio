import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.Leaves
import Development.WeilBound.ThetaLifts.SmallCones.GenSmallOf
import Development.WeilBound.ThetaLifts.SmallCones.Kernel
import Development.WeilBound.ThetaLifts.SmallCones.MixABOf
import Development.WeilBound.ThetaLifts.SmallCones.TwoExp
import Development.WeilBound.ThetaLifts.SmallCones.SliceSummable
import Development.WeilBound.ThetaLifts.SmallCones.NormLeSum
import Development.WeilBound.ThetaLifts.SmallCones.LineInt
import Development.WeilBound.ThetaLifts.SmallCones.SchInt
import Development.WeilBound.ThetaLifts.SmallCones.TateAbs
import Development.WeilBound.ThetaLifts.SmallCones.IntegrableProdOfBound
import Development.WeilBound.ThetaLifts.SmallCones.Unfold
import Development.WeilBound.ThetaLifts.SmallCones.UnipEx
import Development.WeilBound.ThetaLifts.SmallCones.StabDec
import Development.WeilBound.ThetaLifts.SmallCones.WittOf
import Development.WeilBound.ThetaLifts.SmallCones.SplitLatMap
import Development.WeilBound.ThetaLifts.SmallCones.IwaExOf
import Development.WeilBound.ThetaLifts.SmallCones.KFinDataOf
import Development.WeilBound.ThetaLifts.SmallCones.SoStab
import Development.WeilBound.ThetaLifts.SmallCones.FormSwapZero
import Development.WeilBound.ThetaLifts.SmallCones.LinExOf
import Development.WeilBound.ThetaLifts.SmallCones.SoZero

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure Ext : Prop where
  mixW : MixW
  mixX : MixX
  basic : ThetaBasic
  evZero : EvZero
  evCone : EvCone
  stab : StabEx
  pair : PairEx
  plane : PlaneHerm
  top : GrpTop
  eps : EpsOf
  triple : TriplePair
  weil : WeilConv
  dom : DomWeil
  semi : SoSemi
  decay : SoDecay
  vol : FinVolU
  fin : SoFin

theorem thetaExp : ThetaExp := thetaExp_of slice_of

theorem evUniq : EvUniq := evUniq_of thetaExp

theorem Ext.kernel (h : Ext) : CTKernel :=
  ctKernel_of thetaExp evUniq slice_of evAdm_of h.mixW h.mixX h.basic h.pair low_of unipEx_of h.top h.eps

theorem Ext.fub (h : Ext) : CTFub := ctFub_of unipEx_of h.basic h.top h.eps

theorem Ext.mixAB (h : Ext) : MixAB := Ker.mixAB_of h.mixW h.mixX h.evZero h.pair thetaExp evUniq

theorem Ext.coneA (h : Ext) : ConeA :=
  coneA_of unfold_of unipEx_of stabDec_of h.basic h.top h.eps evAdm_of h.mixAB (lineInt_of slice_of schInt tateAbs) h.dom

theorem Ext.coneB (h : Ext) : ConeB :=
  coneB_of unfold_of unipEx_of stabDec_of h.basic h.top h.eps evAdm_of h.mixAB (lineInt_of slice_of schInt tateAbs) h.semi h.vol h.fin soStab_of
    (soEv_of linEx_of low_of)

theorem Ext.genAniso (h : Ext) : GenAniso := genAniso_of h.kernel h.fub h.mixW h.weil h.basic witt_of h.top h.eps

theorem Ext.genBig (h : Ext) : GenBig := genBig_of h.kernel h.fub h.coneA h.mixW h.weil h.basic witt_of h.top h.eps

theorem Ext.genSmall (h : Ext) : GenSmall :=
  genSmall_of h.kernel h.fub h.coneB (Ker.twoExp_of thetaExp) h.mixAB h.mixW h.evCone witt_of stabDec_of unipEx_of h.basic h.top h.eps
    h.decay h.vol h.fin soStab_of (soZeroA'_of linEx_of h.mixX thetaExp evUniq) (soEv_of linEx_of low_of)

theorem ct_all (h : Ext) : CTKernel ∧ SplitEx ∧ CTBigZero ∧ CTSmallZero ∧ CTBigCone ∧ CTSmallCone :=
  have k := kFinData_of h.stab
  have i := iwaEx_of h.stab
  ⟨h.kernel, splitEx_of h.genBig h.genSmall h.genAniso k h.stab i h.pair h.plane h.evCone h.evZero unipEx_of low_of h.triple,
    ctBigZero_of h.genBig h.genAniso k h.stab i h.pair h.plane h.evCone unipEx_of h.triple,
    ctSmallZero_of h.genAniso k h.stab h.triple, ctBigCone_of h.genBig k i h.pair h.evZero unipEx_of h.triple,
    ctSmallCone_of h.genSmall k i h.pair h.evZero unipEx_of h.triple⟩

end PositivityTheory.ThKCT

end

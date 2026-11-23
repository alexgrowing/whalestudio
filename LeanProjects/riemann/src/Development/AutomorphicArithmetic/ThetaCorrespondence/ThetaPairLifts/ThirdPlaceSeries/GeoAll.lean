import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass

set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
section Gen
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word)
set_option maxHeartbeats 1000000 in
structure GeometricFamily where
  g : Geo D
  j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  ι : Type
  v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u g)
  o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u g) k ι
  n : ℕ
  G : Fin n → GLoc v
  pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg
  Q : ∀ PP, _root_.GlobalTheory.Fam.QAllAlt W PP → GlobalTheory.QTw.QGeo v (baseOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g) PP
  d : _root_.GlobalTheory.MiTop.BottomData W u
  c₀ : ℕ → ℂ
attribute [instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
variable {W u} (a : _root_.GlobalTheory.Fam.GeometricFamily W u)
abbrev GeometricFamily.fam (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))) : _root_.GlobalTheory.Fam.FamilyCharacter W u :=
  ⟨a.g, a.j, row, col⟩
structure GeometricFamily.Is : Prop where
  meas : GeoMeas (_root_.GlobalTheory.Fam.pk_z W) a.g
  last : (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).VolLast
  x : ∀ j, j ≤ D.R.m → (a.g.x j).Is
  vis : a.v.Is
  shape : ShapeOff a.v a.o
  gpin : GPin a.G
  tie : ∀ row col, _root_.GlobalTheory.Fam.CommutingVectorTie (a.fam row col) a.v ∧ _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl
  top : _root_.GlobalTheory.Fam.LeadingReadAt W u a.j a.g.bT
  norm : star a.o.ζ₀ ⬝ᵥ a.g.Lz.gram *ᵥ a.o.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) ∧
    ∀ j h, a.v.τ j h *ᵥ a.o.ζ₀ = (-D.host.xi0 ^ (D.R.m / 2)) • (a.g.bes j 0 h).ζ
  stdG : ∀ i, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((a.G i).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (a.G i).FT ∧
    (a.G i).z₀ = fun r => (ofSplit (a.G i).q).pr (a.o.ζ₀ r)
  stdQ : ∀ PP h, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos ((a.Q PP h).FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos (a.Q PP h).FT ∧
    (a.Q PP h).z₀ = fun r => (ofSplit (a.Q PP h).q).pr (a.o.ζ₀ r)
  bot : (∀ h0, a.d.B.lev = (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).B 0 D.R.rS h0) ∧ a.d.b = a.g.b 0 ∧ a.d.B.Adapted (W.S.tr u).wt ∧
    ∀ r, (a.d.B.d.i₀ *ᵥ vecB a.d.B.o a.d.B.ζ) r = W.S.X.ιE (W.S.X.zR u (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) r))
end Gen
section True
open GlobalTheory.Mem GlobalTheory.Mem.Col2
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
structure GeometricFamily.True (a : _root_.GlobalTheory.Fam.GeometricFamily W u) : Prop where
  pinX : GlobalTheory.AdForm.PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ a.g.x a.g.vac a.c₀
  std : @GlobalTheory.AdForm.StdT B X I l Z u a.k a.fld a.val a.top a.loc a.ι (@TDat.p _ _ _ a.fld a.val a.top a.loc _ a.o)
    (@TDat.β _ _ _ a.fld a.val a.top a.loc _ a.o) (@TDat.Q _ _ _ a.fld a.val a.top a.loc _ a.o) fun j => (a.g.x j).L
  emb : GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((a.g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  z0 : ∀ r, vecB (a.g.oT B.R.m rfl) (@TDat.ζ₀ _ _ _ a.fld a.val a.top a.loc _ a.o) r =
    (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)
structure GeometricFamilyConditions (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : Prop where
  xi : ∀ t, ChrEq ((_root_.GlobalTheory.Fam.pk_z W).xi t) (I.xi (W.P.I.tup t))
  Q : ∀ t PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t ↔ PP ∈ Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K)
  top1 : ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt W u j 1
end True
end GlobalTheory.Fam
end
end

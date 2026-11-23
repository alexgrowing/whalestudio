import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top
namespace GlobalTheory.Cp
section Cls
open Formalism.MainNotions.Pk
end Cls
section IndefiniteRowSideFullHecke
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef NumberField IsDedekindDomain
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
end IndefiniteRowSideFullHecke
section At
open Formalism
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : _root_.Formalism.L2.RecTAlt ex} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
structure IndefiniteRealisationConstantBounds (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (C CH : ℝ) (hN hO : Prop) : Prop where
  w1 : ∀ w, (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w → w ∈ Q.Rl.twPl
  covol : ((Q.Rl.toCx3 Q.F).data Q.F.cr false).L3 (Q.Rl.num Q.F C CH)
  onto : hN → ((Q.Rl.toCx3 Q.F).data Q.F.cr false).ON (Q.Rl.num Q.F C CH)
  lamLow : hO → ((Q.Rl.toCx3 Q.F).data Q.F.cr true).L6 (Q.Rl.num Q.F C CH)
  seeIso : (Q.Rl.toCx3 Q.F).SEEIso Q.sEE
  miStar : (Q.Rl.toCx3 Q.F).MIstar2 (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE
  fun0 : hN → ((Q.Rl.toCx3 Q.F).data Q.F.cr false).FUN (Q.Rl.num Q.F C CH)
  pass : Formalism.IndefR.Links.PassIn3 Q.Rl Q.F C CH
  kap : Formalism.L2.Rows.RowsHoldKap3 P
end At
section Serv
open Formalism.MainNotions.Pk Formalism.L2
structure SelectionServed (𝒞 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒞) : Prop where
  twU : Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ∃ LC, WeilJacquetShalikaLaw.CmpV (Fm.ex x hx i).cmp (Fm.X x i) (Fm.ex x hx i).tw (reW (Fm.Gy x i) LC) ∧ SysTw (Fm.D x i) (Fm.L x i)
      (Fm.Gx x i) Fm.GK (Fm.X x i) (reW (Fm.Gy x i) LC) (Fm.ex x hx i).lev (Fm.ex x hx i).errX Fm.cX.err 1
  pdv : Closed 𝒞 fun Fm _ => ∀ (hc : 𝒞 Fm) (x : ℝ) (hx : Fm.x1 < x) (h0 : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    ((((sel Fm hc).2 x hx h0 i).T.ker.ent.UnUnit ∧ OrbitPlaces.KmapRat ((sel Fm hc).2 x hx h0 i).T.ker.ent ∧
        OrbitPlaces.KFi (Fm.D x i) (Fm.ex x hx i).tw ∧ OrbitPlaces.Stab0 (Fm.D x i)) ∧
      ∃ (ep : _) (be : _) (sg : _),
        OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.OrbitBoundWithoutOperator (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.Gx x i) Fm.GK ∧
        OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg) (Fm.X x i) ∧
        OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i)
          (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) ((sel Fm hc).2 x hx h0 i).T.ker.ent ep be sg))
end Serv
end GlobalTheory.Cp
namespace GlobalTheory.Fc.R1
open GlobalTheory.Fc GlobalTheory.Cp
def P_hRB_alt : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows b.B
def SlotRowBoundCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.P_hRB_alt)
def TwistBundleCondition : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  Formalism.L2.DIV.TieTwRec O.L b.P.S0.Tw
def SlotTwistCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.TwistBundleCondition)
def PrimitivityBundleCondition : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3
def SlotPrimitivityCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.PrimitivityBundleCondition)
def LambdaPrimeBundleCondition : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  Formalism.L2.Rows.RowsHoldLam3 b.P
def SlotLambdaPrimeCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.LambdaPrimeBundleCondition)
def DivisorBundleCondition : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  DivRows3G b.P
def SlotDivisorCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.DivisorBundleCondition)
def DecompositionPointBundle : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  DcPtG b.P
def SlotDecompositionPointCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.DecompositionPointBundle)
def SelectionJumpBundleCondition : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin (R := b.R) (S := b.S) (Q := b.B.Q))
def SlotSelectionJumpCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (AtAll _root_.GlobalTheory.Fc.R1.SelectionJumpBundleCondition)
def LeafUniqueMap {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : Prop :=
  ∀ j, Formalism.IndefR.FWT.OneMapRowR b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ b.B.O (Formalism.IndefR.phEff b.B.Q.Rl) j
abbrev DefiniteSideType : Type 1 := ∀ (D : D7) (O : Obj D) (c : ℝ), _root_.GlobalTheory.Fc.BundleCondition D O c → ℝ → ℝ → Prop
def SelectionDefiniteRows (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Prop :=
  Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, ∃ C : ℝ, 0 ≤ C ∧ _root_.GlobalTheory.Cp.EventuallyAlongSelection (_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc) fun x hx _ i =>
    _root_.GlobalTheory.Cp.IndefiniteRealisationConstantBounds (σ Fm (d3_a hc) x hx i).B.Q C CH (DIVinN Fm) (_root_.GlobalTheory.Fc.R1.LeafUniqueMap (σ Fm (d3_a hc) x hx i)) ∧ DR _ _ _ (σ Fm (d3_a hc) x hx i) C CH
def SlotDefiniteRowsCondition (DR : _root_.GlobalTheory.Fc.R1.DefiniteSideType) (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (_root_.GlobalTheory.Fc.R1.SelectionDefiniteRows DR)
def SelectionLpBound (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Prop :=
  Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨((_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)).1, fun x hx h i => ((_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) Fm (d3_a hc) x hx h i).toSTies⟩)
def SlotLpCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (_root_.GlobalTheory.Fc.R1.SelectionLpBound)
def SelectionOrderBound (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Prop :=
  Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨((_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)).1, fun x hx h i => ((_root_.GlobalTheory.Fc.spectralConditionOfRawSelection σ) Fm (d3_a hc) x hx h i).toSTies⟩
def SlotOrderCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (_root_.GlobalTheory.Fc.R1.SelectionOrderBound)
def SelectionServesFamily (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Prop :=
  _root_.GlobalTheory.Cp.SelectionServed (D3 3 𝒜) fun Fm hc => (_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)
def SlotServiceCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (_root_.GlobalTheory.Fc.R1.SelectionServesFamily)
def SelectionZeroLocus (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜) : Prop :=
  Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : ((_root_.GlobalTheory.Fc.familySelection σ) Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.A3.A ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.P0
          ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.ψ0 (((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.Zs) k
          ((_root_.GlobalTheory.Fc.baseLevelChoiceOfRawSelection σ) Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec
def SlotZeroLocusCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk (_root_.GlobalTheory.Fc.R1.SelectionZeroLocus)
def SlotTorsionFreeCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := Row Q Lk fun 𝒜 _ => H_hTF 𝒜
def CountsIrreducibilityConstants' (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) : Prop := ∃ (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants) (cIc : ℝ),
  (∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A) ∧ 0 < cIc ∧
  Row Q Lk fun 𝒜 _ => (Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb) ∧
    (Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f))
def SlotNormCondition (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition) (N : FamClass → Prop) : Prop := Row Q Lk fun 𝒜 _ => N (D3 3 𝒜)
end GlobalTheory.Fc.R1
end
end

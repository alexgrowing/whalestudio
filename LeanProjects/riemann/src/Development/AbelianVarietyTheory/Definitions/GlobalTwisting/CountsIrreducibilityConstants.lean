import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Formalism.LocalToGlobal.Divisibility.LinkDefN
import Formalism.SharpRestriction.SmoothDesignExistence.SumOverPrimesHypotheses
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
import Formalism.LocalToGlobal.GlobalTheory.ConcNP
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.CountT
import Formalism.SharpRestriction.DesignExistsOfChoices
import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
import Formalism.SharpRestriction.PageFix
import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
import Formalism.SharpRestriction.LevelLetterCocycles.TwAllF
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top

namespace GlobalTheory.Cp

section Cls

open Formalism.MainNotions.Pk

abbrev WithChN (𝒞 : FamClass) : FamClass :=
  fun Fm => 𝒞 Fm ∧ DGamDvdF Fm ∧ TameDistinctF Fm ∧ BoxesF Fm ∧ QDRowsF Fm ∧ Fm.CYL ≤ 9

abbrev D3 (C0 : ℝ) (𝒜 : FamClass) : FamClass := Des (WithChN 𝒜) C0

theorem d3_a {C0 : ℝ} {𝒜 : FamClass} {eps : ℝ} {Fm : FamP eps} (h : D3 C0 𝒜 Fm) : 𝒜 Fm := h.1.1.1.1

def TupUsedF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x), ∀ μ : (Fm.D x i).what₂.Tup, Formalism.BasicNotions.DV.Used (Fm.D x i) μ

def TwAllF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
      ∃ (N0 : (Fm.D x i).ntw.Tw → ℕ) (S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)),
        Formalism.MainNotions.TwGoodAtAll (Fm.D x i) (Fm.ex x hx i).nch ⟨Formalism.MainNotions.twE Fm x hx i, N0, S⟩

def Duty {eps : ℝ} (Fm : FamP eps) : Prop :=
  PageFix Fm ∧ PageWin Fm ∧ Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧ TameDistinctF Fm ∧ ChosenWall Fm ∧ TupUsedF Fm ∧ TwAllF Fm

end Cls

section IndefiniteRowSideFullHecke

open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef NumberField IsDedekindDomain

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

def RationalLiftSpanAtUsedTuples (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    Formalism.BasicNotions.Idx.Z0 D (P.I.tup t) ((i : ℕ) + 1) =
    Submodule.span ℂ (Set.range fun k =>
      (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1))
        (P.I.eMt i t ((lZ0 D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec (Pi.single k 1))))

def ThThetaG (P : RowSideFamily ex) : Prop :=
  ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ x,
    D.what₂.thetaP (P.I.tup t) ((i : ℕ) + 1) (D.what₂.jMt (P.I.tup t) ((i : ℕ) + 1) (P.I.eMt i t x)) =
      P.I.jW i (((P.A3.indefDown P.S0).θ i t).mulVec ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i t).mulVec x))

def DcPtG (P : RowSideFamily ex) : Prop :=
  ∀ (u : D.what₂.Word) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) →
    ∀ (x : Fin (P.Dc.a (P.I.wU u)) → D.what₂.LL) (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
    D.what₂.embLL (P.Dc.Pt (P.I.wU u) t x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (P.I.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))

open Classical in

structure NumTieG (P : RowSideFamily ex) : Prop where
  Ij : ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ w,
    D.what₂.Ij (P.I.tup t) ((i : ℕ) + 1) w = (P.A3.indefDown P.S0).Iw i t (D.plEq w)
  jw : ∀ (i : Fin D.R.m) (t : P.T), Formalism.IndefR.RecTie.Used0 D (P.I.tup t) → ∀ w,
    D.what₂.jw (P.I.tup t) ((i : ℕ) + 1) w =
      Formalism.DivisionValues.jw ((P.A3.A.side P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs)).HT i t) (D.plEq w)
        ((P.A3.A.side P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs)).Tl i t)
  etaJ : ∀ (i : Fin D.R.m) w, D.what₂.etaJ ((i : ℕ) + 1) w =
    if D.plEq w ∈ (P.A3.indefDown P.S0).Tw then
      P.A3.A.fam.etaJ P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i ((P.A3.indefDown P.S0).μ (D.plEq w)) (D.plEq w) else 0

structure DivRows3G (P : RowSideFamily ex) : Prop where
  sharpRR : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (P.A3.indefDown P.S1).RR (P.A3.indefDown P.S1).XE P.I.eRR
  baseRR : HLatTie ex.p0.s.RR (P.A3.indefDown P.S0).RR (P.A3.indefDown P.S0).XE P.I.eRR0
  divisionRows_rationalLift : RationalLiftSpanAtUsedTuples P
  thTheta : ThThetaG P
  num : NumTieG P
  colsBk : ∀ u x y, D.div.Bk u (P.I.eNu u x) (P.I.eRR y) =
    (P.A3.colData2 P.C (fun _ => ⊥) (fun _ _ => ⊥) (fun _ _ _ _ => 0)).B (P.I.wU u) x y

end IndefiniteRowSideFullHecke

section At

open Formalism

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : Formalism.L2.RecT ex} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure RowsAt4 (Q : Formalism.IndefR.RealT Rc P Dcf Spf Zscf S Ks) (C CH : ℝ) (hN hO : Prop) : Prop where
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

structure ServT (𝒞 : FamClass) (sel : TSel 𝒞) : Prop where
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

def P_hRB : BdP Bundle := fun D O _ b =>
  Formalism.IndefR.RowsB b.B

def RankBoundAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (AtAll P_hRB)

def P_hTw : BdP Bundle := fun D O _ b =>
  Formalism.L2.DIV.TieTwRec O.L b.P.S0.Tw

def TwistConditionAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (AtAll P_hTw)

def P_hPA : BdP Bundle := fun D O _ b =>
  Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3

def PeriodAdmissibilityAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (AtAll P_hPA)

def P_hLamP : BdP Bundle := fun D O _ b =>
  Formalism.L2.Rows.RowsHoldLam3 b.P

def LambdaPositivityAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (AtAll P_hLamP)

def P_hDivG : BdP Bundle := fun D O _ b =>
  DivRows3G b.P

def DivisorConditionAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (AtAll P_hDivG)

def P_hDcPtG : BdP Bundle := fun D O _ b =>
  DcPtG b.P

def DecompositionConditionAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (AtAll P_hDcPtG)

def P_selJ : BdP Bundle := fun D O _ b =>
  Nonempty (Formalism.L2.SG.JoinSI.JoinSI (R := b.R) (S := b.S) (Q := b.B.Q))

def JSelectionAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (AtAll P_selJ)

def OneMap {D : D7} {O : Obj D} {c : ℝ} (b : Bundle D O c) : Prop :=
  ∀ j, Formalism.IndefR.FWT.OneMapRowR b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ b.B.O (Formalism.IndefR.phEff b.B.Q.Rl) j

abbrev DefT : Type 1 := ∀ (D : D7) (O : Obj D) (c : ℝ), Bundle D O c → ℝ → ℝ → Prop

def H_rRows (DR : DefT) (𝒜 : FamClass) (σ : RawSel Bundle 𝒜) : Prop :=
  Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, ∃ C : ℝ, 0 ≤ C ∧ EvSel (sel σ) Fm (d3_a hc) fun x hx _ i =>
    RowsAt4 (σ Fm (d3_a hc) x hx i).B.Q C CH (DIVinN Fm) (OneMap (σ Fm (d3_a hc) x hx i)) ∧ DR _ _ _ (σ Fm (d3_a hc) x hx i) C CH

def RestRowsConditionAtBundlePoints (DR : DefT) (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (H_rRows DR)

def H_sLp (𝒜 : FamClass) (σ : RawSel Bundle 𝒜) : Prop :=
  Formalism.L2.SG.ThmSOwn.LoopRowS 3 (D3 3 𝒜) (fun Fm hc => ⟨((sel σ) Fm (d3_a hc)).1, fun x hx h i => ((selS σ) Fm (d3_a hc) x hx h i).toSTies⟩)

def LpSelectionAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (H_sLp)

def H_sO (𝒜 : FamClass) (σ : RawSel Bundle 𝒜) : Prop :=
  Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, Formalism.L2.SG.ThmSOwn.TheoremSSelected Fm 3
      ⟨((sel σ) Fm (d3_a hc)).1, fun x hx h i => ((selS σ) Fm (d3_a hc) x hx h i).toSTies⟩

def IntegralSelectionAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (H_sO)

def H_hServ (𝒜 : FamClass) (σ : RawSel Bundle 𝒜) : Prop :=
  ServT (D3 3 𝒜) fun Fm hc => (sel σ) Fm (d3_a hc)

def SerreConditionAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (H_hServ)

def H_zL (𝒜 : FamClass) (σ : RawSel Bundle 𝒜) : Prop :=
  Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, ∃ xr : ℝ, ∀ x (hx : Fm.x1 < x) (h : ((sel σ) Fm (d3_a hc)).1 ≤ x), xr ≤ x →
      ∀ (i : Fm.Ix x) (k : Fin (Fm.D x i).R.m),
        Function.Surjective (Formalism.L2.DIV.lPrj (Fm.D x i) ((selP σ) Fm (d3_a hc) x hx h i).1.A3.A ((selP σ) Fm (d3_a hc) x hx h i).1.P0
          ((selP σ) Fm (d3_a hc) x hx h i).1.ψ0 (((selP σ) Fm (d3_a hc) x hx h i).1.A3.fam3.toSub2 ((selP σ) Fm (d3_a hc) x hx h i).1.Zs) k
          ((selP σ) Fm (d3_a hc) x hx h i).1.A3.A.μ0).mulVec

def LZeroConditionAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk (H_zL)

def H_hTF (𝒜 : FamClass) : Prop :=
  Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3

def TorsionFreenessAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) : Prop := Row Q Lk fun 𝒜 _ => H_hTF 𝒜

def H_hTu (cT : ℝ → ℝ → ℝ) (𝒜 : FamClass) : Prop :=
  Closed (WithTw (WithSm (WithChN 𝒜))) fun {eps} Fm _ => cT eps Fm.CYL ≤ Fm.CTu → TuSize Fm

def CountsIrreducibilityConstants (Q : V4.Slot) (Lk : LkT Bundle) : Prop := ∃ (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants) (cIc : ℝ),
  (∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A) ∧ 0 < cIc ∧
  Row Q Lk fun 𝒜 _ => (Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.S.CountE.CountAllPointsClass Formalism.L2.SG.ThmSOwn.PLevT' Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A
      (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb) ∧
    (Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f))

def PredicateAtBundlePoints (Q : V4.Slot) (Lk : LkT Bundle) (N : FamClass → Prop) : Prop := Row Q Lk fun 𝒜 _ => N (D3 3 𝒜)

end GlobalTheory.Fc.R1

end

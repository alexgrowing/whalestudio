import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataDIVDefs
import Formalism.SharpRestriction.Divisibility.HeightShare
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.SharpRestriction.Divisibility.ProductFirstParts
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.WeightFamilies
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.sizeConstantAtParamsWeight

open Formalism.BasicNotions NumberField Finset

structure ThFin where
  l : ℕ
  q : ℕ
  DF : ℕ
  r1 : ℕ
  phic : ℝ
  lamQ : ℝ
  nuLoc : ℝ
  minVTheta : ℝ
  vTau : ℝ

structure ThArch where
  q : ℕ
  DF : ℕ
  r1 : ℕ
  phic : ℝ
  logThetaMax : ℝ
  cuspVal : ℝ

structure JacNum where
  p : ℕ
  c : ℕ
  jac : ℝ

structure MajNum where
  lmin : ℝ
  lmax : ℝ

structure Loc (D : D7) (V : DivX D) (Lc : placeRankTwoOne.Loc D V) where

  NNH : ℕ → HLat D.what₂.LL
  inc : ∀ j, (V.MjH j).V →ₗ[D.what₂.LL] (NNH j).V
  inc_inj : ∀ j, Function.Injective (inc j)

  inc_lat : ∀ j x, x ∈ (V.MjH j).L ↔ inc j x ∈ (NNH j).L

  inc_metric : ∀ j v x, Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (V.MjH j).b (V.MjH j).X v x) =
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (NNH j).b (NNH j).X v (inc j x))

  goodE : ∀ j, (NNH j).V →ₗ[D.what₂.LL] (NNH j).V
  goodE_idem : ∀ j, goodE j ∘ₗ goodE j = goodE j
  goodE_range : ∀ j y, y ∈ LinearMap.range (inc j) ↔ goodE j y = y

  l1 : ∀ j c, D.what₂.Tau → ∀ w, Lc.PtF j c w → ℝ

  l2 : ∀ j c, D.what₂.Tau → ∀ w, Lc.PtF j c w → ℝ

  eV : ArithmeticCylinders.VecAt D

  ThF : Type
  thF : ThF → ThFin
  ThA : Type
  thA : ThA → ThArch

  JB : Type
  jb : JB → JacNum

  Maj : Type
  maj : Maj → MajNum

variable (D : D7) (L : SizeData₂ D) (V : DivX D) (P : DIV.Align.PrinLev V) (Lc : placeRankTwoOne.Loc D V) (B : WeightFamilies.Prov D) (X : Loc D V Lc)

def PP (CP AP : ℝ) : ℝ := placeRankTwoOne.PP D L CP AP

def RR (Crr : ℝ) : ℝ := WeightFamilies.RRv D Crr

def rkLie (j : ℕ) : DV.EmbC D → ℕ
  | Sum.inl _ => (D.R.sigW j).1
  | Sum.inr _ => (D.R.sigW j).2

def HidaSetting (Cn CP AP Cq : ℝ) (j : ℕ) (w : D.what₂.Tau → ℤ) : Prop := placeRankTwoOne.SizeSettingLemmaThree D L Cn CP AP Cq j w

def Conclusion1 (Cn CP AP Cq C : ℝ) : Prop :=
  ∀ j (w : D.what₂.Tau → ℤ), HidaSetting D L Cn CP AP Cq j w → 0 < (V.MjH j).rank →
    placeRankTwoOne.mainT D V j w - C * placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j w - L.sc.b ≤
      HeightShare.degL (V.MjH j) / ((V.MjH j).rank : ℝ)

def Conclusion2 (Cn CP AP Cq C : ℝ) : Prop :=
  ∀ j (w : D.what₂.Tau → ℤ), HidaSetting D L Cn CP AP Cq j w → (X.NNH j).Good → 0 < (X.NNH j).rank →
    placeRankTwoOne.mainT D V j w - C * placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j w - L.sc.b ≤
      HeightShare.degL (X.NNH j) / ((X.NNH j).rank : ℝ)

def adm1 (C : ℝ) : Prop := HeightShare.Conclusion1 D V C

def ShareLowerBound : Prop := HeightShare.Conclusion2 D V

def PlancherelDifferenceBound : Prop := HeightShare.PointsLemma D V

def adm2 (C : ℝ) : Prop := product_first_partition.Conclusion1 D L V P C ∧ product_first_partition.ApproximantLimitFormula D V P ∧ product_first_partition.Conclusion2 D V P

def ProportionalityIdentity : Prop := WeightThresholdDefs.adm10 V

def adm3 : Prop :=
  (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (c : V.Comp j) (τ : D.what₂.Tau) (w : D.what₂.places.Pl) (y : Lc.PtF j c w),
    0 ≤ X.l1 j c τ w y ∧
    X.l1 j c τ w y ≤ ((D.R.sigW j).1 : ℝ) / ((D.what₂.places.resChar w : ℝ) - 1) ∧
    0 ≤ X.l2 j c τ w y ∧
    (DV.UnramE D (D.what₂.places.resChar w) →
      X.l2 j c τ w y ≤ ((D.R.sigW j).2 : ℝ) / ((D.what₂.places.resChar w : ℝ) - 1) ∧
      X.l2 j c τ w y - X.l1 j c τ w y =
        (∑' n : ℕ, (D.what₂.places.resChar w : ℝ) ^ (-((n : ℤ) + 1)) *
          (rkLie D j (DV.frobEmb D (D.what₂.places.resChar w) (n + 1) (Sum.inl τ)) : ℝ)) -
        ((D.R.sigW j).1 : ℝ) / ((D.what₂.places.resChar w : ℝ) - 1)) ∧
    (D.what₂.places.resChar w ∈ D.host.small ∨ D.what₂.places.resChar w = D.host.q →
      X.l1 j c τ w y ≤ ((D.R.sigW j).2 : ℝ) *
        (1 / ((D.what₂.places.resChar w : ℝ) - 1) + V.vdd (D.what₂.places.resChar w) τ))) ∧
  placeRankTwoOne.RamifiedDeterminantBound D V Lc

def ArchimedeanSignatureMatching : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (c : V.Comp j) τ, V.degHH j c τ = -placeRankTwoOne.c1 D V j τ

def FrobeniusOrbitPlaceCountCondition : Prop := placeRankTwoOne.FrobeniusOrbitPlaceCount D L V

def JetHyp (q DF : ℕ) : Prop :=
  (DF : ℝ) * (2 * Real.sqrt (2 * (D.R.f : ℝ) * (D.R.m : ℝ))) < (q : ℝ) ∧ 3 * DF + 2 ≤ q

def QNorm (q : ℕ) : Prop :=
  Odd q ∧ ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧ (π : D.host.E) * D.host.conj (π : D.host.E) = (q : D.host.E)

def ThetaLevelCondition (CP AP Crr : ℝ) (q DF : ℕ) : Prop :=
  RR D Crr ^ 4 * PP D L CP AP ^ 3 * (DF : ℝ) ^ 2 ≤ (q : ℝ) ∧ (placeRankTwoOne.dimY D + 4) * DF + 2 ≤ q

def TheoremI2Hypotheses (CP AP Crr : ℝ) (q DF : ℕ) : Prop :=
  1 ≤ DF ∧ Real.log (q : ℝ) ≤ L.sc.L ^ 2 ∧ ThetaLevelCondition D L CP AP Crr q DF

def adm5 (CP AP Crr : ℝ) : Prop :=
  (∀ s : X.ThF, (X.thF s).l.Prime → 0 < (X.thF s).q →
    (X.thF s).lamQ ^ 2 ≤ RR D Crr * PP D L CP AP * (X.thF s).phic ∧
    (ModuliIntegralCharts.NHyp D (X.thF s).l (X.thF s).q → JetHyp D (X.thF s).q (X.thF s).DF →
      (X.thF s).minVTheta ≤ (X.thF s).nuLoc +
        RR D Crr * PP D L CP AP * ((X.thF s).DF : ℝ) ^ 2 / ((X.thF s).q : ℝ) * (X.thF s).phic) ∧
    ((X.thF s).r1.Prime → (X.thF s).r1 ≠ 2 → jacobiSym (-(D.host.d : ℤ)) (X.thF s).r1 = 1 →
      Nat.Coprime (X.thF s).r1 (X.thF s).q → ((X.thF s).r1 : ℝ) ≤ L.sc.L →
      ((X.thF s).r1 : ℝ) ^ (-(4 : ℤ)) * (X.thF s).phic -
        (if (X.thF s).l = (X.thF s).r1 then PP D L CP AP else 0) ≤ (X.thF s).vTau)) ∧
  (∀ s : X.ThA, 0 < (X.thA s).q → QNorm D (X.thA s).q → TheoremI2Hypotheses D L CP AP Crr (X.thA s).q (X.thA s).DF →
    -(PP D L CP AP * (X.thA s).DF) -
        RR D Crr * PP D L CP AP * ((X.thA s).DF : ℝ) ^ 2 / ((X.thA s).q : ℝ) * (X.thA s).phic
      ≤ (X.thA s).logThetaMax ∧
    ((X.thA s).r1.Prime → (X.thA s).r1 ≠ 2 → jacobiSym (-(D.host.d : ℤ)) (X.thA s).r1 = 1 →
      Nat.Coprime (X.thA s).r1 (X.thA s).q → ((X.thA s).r1 : ℝ) ≤ L.sc.L →
      ((X.thA s).r1 : ℝ) ^ (-(4 : ℤ)) * (X.thA s).phic - PP D L CP AP ≤ (X.thA s).cuspVal))

def MinkowskiSubgroupOrderBound (CG AG : ℝ) : Prop := WeightFamilies.adm2 L B CG AG

def CuspFormNonvanishingSource (Cf Af : ℝ) : Prop := WeightFamilies.Conclusion1 L B Cf Af

def adm6 : Prop :=
  ∀ s : X.JB, (X.jb s).p.Prime → (X.jb s).jac ≤
    ((X.jb s).p : ℝ) ^ ((placeRankTwoOne.dimY D : ℝ) * ((X.jb s).c + 2 + 3 * ⨆ τ, V.vdd (X.jb s).p τ))

def adm7 : Prop := ArithmeticCylinders.LocalShareExpBound D X.eV L.sc.x L.sc.ez

def law7 (CL : ℝ) : Prop := ArithmeticCylinders.lawL D X.eV CL

def adm8 : Prop := HeightShare.adm7 D V ∧ product_first_partition.adm14 D V P

def adm9 (CP AP Crr : ℝ) : Prop :=
  ∀ s : X.Maj, 0 < (X.maj s).lmin → (X.maj s).lmax ≤ RR D Crr * PP D L CP AP / (X.maj s).lmin

def adm10 : Prop := WeightThresholdDefs.proposition_eleven_one_at_scale V P

def adm11 : Prop := HeightShare.Conclusion4 D V ∧ HeightShare.Conclusion5 D V ∧ HeightShare.Conclusion6 D V

def adm12 : Prop := DIV.Align.FanAt D V P

def adm13 : Prop := DIV.Align.FanArAt D V P

def admitted (C1 C2 CG AG Cf Af Ca Aa Ra : ℝ) : Prop :=
  adm1 D V C1 ∧ ShareLowerBound D V ∧ PlancherelDifferenceBound D V ∧ adm2 D L V P C2 ∧ ProportionalityIdentity D V ∧ adm3 D V Lc X ∧ ArchimedeanSignatureMatching D V ∧
    FrobeniusOrbitPlaceCountCondition D L V ∧ adm5 D L V Lc X Ca Aa Ra ∧ MinkowskiSubgroupOrderBound D L B CG AG ∧ CuspFormNonvanishingSource D L B Cf Af ∧ adm6 D V Lc X ∧
    adm7 D L V Lc X ∧ adm8 D V P ∧ adm9 D L V Lc X Ca Aa Ra ∧ adm10 D V P ∧ adm11 D V ∧ adm12 D V P ∧ adm13 D V P

def Stmt (C1 C2 CG AG Cf Af Ca Aa Ra Cn CP AP Cq C : ℝ) : Prop :=
  admitted D L V P Lc B X C1 C2 CG AG Cf Af Ca Aa Ra →
    Conclusion1 D L V Cn CP AP Cq C ∧ Conclusion2 D L V Lc X Cn CP AP Cq C

structure LocF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) where
  fl : placeRankTwoOne.LocF Fm
  cf : WeightFamilies.ProvF Fm
  lo : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i) (fl x hx i)

def LocF.eVT {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} (Y : LocF Fm) : ∀ x (i : Fm.Ix x), ArithmeticCylinders.VecAt (Fm.D x i) :=
  fun x i => if h : Fm.x1 < x then (Y.lo x h i).eV else 0

theorem LocF.eVT_eq {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} (Y : LocF Fm) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    Y.eVT x i = (Y.lo x hx i).eV := dif_pos hx

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm) (Y : LocF Fm)

def ConclusionF1 (Cn CP AP Cq C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i : Fm.Ix x, Conclusion1 (Fm.D x i) (Fm.L x i) (Fm.X x i) Cn CP AP Cq C

def ConclusionF2 (Cn CP AP Cq C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    Conclusion2 (Fm.D x i) (Fm.L x i) (Fm.X x i) (Y.fl x hx i) (Y.lo x hx i) Cn CP AP Cq C

def AdmF (C1 C2 CG AG Cf Af Ca Aa Ra : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    admitted (Fm.D x i) (Fm.L x i) (Fm.X x i) (PL x hx i) (Y.fl x hx i) (Y.cf x hx i) (Y.lo x hx i) C1 C2 CG AG Cf Af Ca Aa Ra

def IdempotentLocalLawFamily (CL : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    law7 (Fm.D x i) (Fm.X x i) (Y.fl x hx i) (Y.lo x hx i) CL

def KudlaFamilyStatement (C1 C2 CG AG Cf Af Ca Aa Ra Cn CP AP Cq C : ℝ) : Prop :=
  AdmF Fm PL Y C1 C2 CG AG Cf Af Ca Aa Ra → ConclusionF1 Fm Cn CP AP Cq C ∧ ConclusionF2 Fm Y Cn CP AP Cq C

end Fam

abbrev LocClass : Type 1 := ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps), LocF Fm → Prop

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) (𝒬 : DIV.Align.PrinLevClass) (𝒴 : LocClass) : Prop :=
  ∀ C1 C2 CG AG Cf Af Ca Aa Ra : ℝ, ∃ Cq C : ℝ,
    Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ PL, 𝒬 Fm PL → ∀ Y : LocF Fm, 𝒴 Fm Y →
      KudlaFamilyStatement Fm PL Y C1 C2 CG AG Cf Af Ca Aa Ra (Fm.CYL + 1) Fm.CP Fm.eP Cq C)

end Formalism.MainNotions.sizeConstantAtParamsWeight

end

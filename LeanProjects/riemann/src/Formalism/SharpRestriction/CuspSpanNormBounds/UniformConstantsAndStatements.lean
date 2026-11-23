import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.SharpRestriction.CuspSpanNormBounds.RotatedWeightedBound
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

namespace Formalism.MainNotions.UniformConstantsAndStatements

export Formalism.MainNotions.S.UnitaryVolumeMass (Kng scalG)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants ValuativeRel IsDedekindDomain NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsNormFrame (D : D7) {T T' : D.host.E} (Λ : Cnt.LatV D) (F : Lat.LFlag (Lat.hS D) D.R.rS T)
    (F' : Lat.LFlag (Lat.hS D) D.R.rS T') : Prop :=
  Lat.IsLift Λ F' ∧ Lat.AdmWit Λ (Lat.gS D) F F' 1 ∧ FrameOK D Λ F'

def EZ (D : D7) {T : D.host.E} (T' : D.host.E) (Λ : Cnt.LatV D) (F : Lat.LFlag (Lat.hS D) D.R.rS T) (Z : Cnt.GramM D) :
    Set (Lat.LFlag (Lat.hS D) D.R.rS T') :=
  {F' | IsNormFrame D Λ F F' ∧ Lat.IsGeneric Λ (Lat.gS D) F F' ∧ Lat.ZhatL F F' = Z}

def cntZ (D : D7) {T : D.host.E} (T' : D.host.E) (Λ : Cnt.LatV D) (F : Lat.LFlag (Lat.hS D) D.R.rS T) (Z : Cnt.GramM D) :
    ℕ∞ :=
  Cnt.cntCl (EZ D T' Λ F Z) fun F' F'' =>
    ∃ n ∈ Lat.NLam Λ F, (∀ a, n (Lat.frame F a) = Lat.frame F a) ∧ ∀ b, n (Lat.frame F' b) = Lat.frame F'' b

def nuTot (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E))
    (what₂ : Finset (Cnt.LatV D)) (Z : Cnt.GramM D) : ℝ≥0∞ :=
  ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (cntZ D ((Lat.Tu D u' : ℕ) : D.host.E) Λ (lf D F0) Z : ℝ≥0∞)

structure LargenessConstants where
  C0 : ℝ
  C' : ℝ
  Cl : ℝ
  Cg : ℝ
  cb : ℝ
  Cu : ℝ
  cT : ℝ
  CT : ℝ

def Hyp (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) : Prop :=
  StandingNumericalData D h.C0 ∧ StandingHypotheses D large₂ h.C' h.Cl h.Cg h.cb h.Cu h.cT h.CT ∧ 1 ≤ h.C0

def adm1 (D : D7) : Prop :=
  4 * D.R.rS + 8 ≤ D.R.k →
  ∃ (δ : ∀ p : LocalSplitGroups.PlF D, (D.s.atP p).Fp) (M : ∀ p : LocalSplitGroups.PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, LocalSplitGroups.Agree δ M p) ∧
    ∀ p (x : D.host.E), (D.s.atP p).psiE ((D.s.atP p).ιE (-(x / (Lat.gS D : D.host.E)))) =
      (M p).L.psi0 (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (x * (LocalSplitGroups.uP p : D.host.E)) *
        Ring.inverse (LocalSplitGroups.qE p))

def adm2 (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) : Prop :=
  Hyp D large₂ h → UnitaryVolumeMass.cExp D

def adm3 (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) : Prop :=
  Hyp D large₂ h → UnitaryVolumeMass.cIdOne D

def ArchimedeanSignatureMatching (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) : Prop :=
  Hyp D large₂ h → UnitaryVolumeMass.c2aG D

def adm5 (D : D7) (C : ℝ) : Prop :=
  UnitaryVolumeMass.stNG D C

def adm6 (D : D7) (Ch Cg Cb : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : ThB.Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ),
    ThB.LocOk D Ch Cg L L.lam ka b 1 → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ γ : Point ℂ (D.R.rS + 1), ThB.Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 →
      ThB.BpIneq D Cb L f μsec b γ

def TelescopingFormStatement (D : D7) (Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : ThB.BData D Ch Cg T T' b 0),
    ThB.BSumRot D X (fun _ => 1) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        ThB.jSqG D X

def ConjugateSelfDualCharacter (D : D7) (C : ℝ) : Prop :=
  ∀ T T' : ℕ, 1 ≤ T → 1 ≤ T' →
    ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // ThB.IsBPt D T T' γ}, ENNReal.ofReal (ThB.wPt D γ.1)⁻¹ ≤
      ENNReal.ofReal (C ^ (Fintype.card D.what₂.Tau * (D.R.rS + 1)))

def TheoremBWeightedBound (D : D7) (Aw Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : ThB.BData D Ch Cg T T' b 0),
    (∀ v, ThB.AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) →
    ThB.BSumRot D X (fun γ => ThB.normWt D T T' γ ^ (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        ThB.jSqG D X

def adm8 (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (C Ce : ℝ) : Prop :=
  Hyp D large₂ h → ∀ u u' : D.what₂.Word,
    ∃ (cInf : ℝ) (constP : HeightOneSpectrum (𝓞 D.host.F) → ℝ)
      (dens : Cnt.GramM D → HeightOneSpectrum (𝓞 D.host.F) → ℝ),
      0 < cInf ∧ (∀ p, 0 < constP p) ∧ Multipliable constP ∧ 0 < ∏' p, constP p ∧
      (∀ Z p, |dens Z p - 1| ≤ C * (Ideal.absNorm p.asIdeal : ℝ) ^ (-((D.R.k : ℝ) - 2 * D.R.rS - 3))) ∧
      (∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
        ∀ what₂ : Finset (Cnt.LatV D), IsRowReps D F0 what₂ →
        ∀ Z : Cnt.GramM D, (∀ τ, 0 < Cnt.Gz D (Tr D u) (Tr D u') Z τ) →
          (∃ Λ ∈ what₂, ∃ F' : Cnt.FlagU D u', IsNormFrame D Λ (lf D F0) F' ∧ Lat.ZhatL (lf D F0) F' = Z) →
          Multipliable (dens Z) ∧
          nuTot D u u' F0 what₂ Z =
            ENNReal.ofReal (cInf * (∏' p, constP p) * (∏' p, dens Z p) *
              ∏ τ, Cnt.Gz D (Tr D u) (Tr D u') Z τ ^ ((D.R.k : ℝ) - 1))) ∧
      ∀ θ : ℝ, 0 < θ → ∀ W : D.what₂.Tau → LocW D.R.k D.R.rS, (∀ τ, GoodW D τ u u' θ (W τ)) →
        ∀ A : ∀ τ, LocS (W τ), (∀ τ, GoodS D (lamD D τ) (A τ)) → (∀ τ, (A τ).deg = D.dsig τ) →
        ∀ μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
          (∀ τ, IsSection D.R.k D.R.rS (W τ).z (W τ).z' (μsec τ)) →
          ENNReal.ofReal (gaG D * (cInf * ∏' p, constP p)) * ∏ τ, MMv D u u' (A τ) (μsec τ) ≤
            ENNReal.ofReal (θ ^ (2 * Fintype.card D.what₂.Tau) *
              large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * (Fintype.card D.what₂.Tau : ℝ)) *
              ((1 + eSum D Ce) * ((D.duS u : ℝ) * (D.duS u' : ℝ)) / D.what₂.Dstar))

def adm9 (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (C1 c : ℝ) : Prop :=
  Hyp D large₂ h → C1 * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) ≤ D.R.k * Real.log D.R.k → ∀ u u', UnitaryVolumeMass.LoopPairSumBound D u u' c

def Conclusion1 (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (c C : ℝ) : Prop :=
  Hyp D large₂ h → UnitaryVolumeMass.NonGenericKernelBound D large₂ c C

def Conclusion2 (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (C : ℝ) : Prop :=
  Hyp D large₂ h → UnitaryVolumeMass.GenericScalarPairSum D large₂ C

structure AdmC where

  CNG : ℝ

  Ch : ℝ
  Cg : ℝ
  Cb : ℝ
  secondBesselConstant : ℝ
  Aw : ℝ
  Cgw : ℝ
  Cbw : ℝ

  CM : ℝ
  Ce : ℝ

  C1 : ℝ
  cL : ℝ

structure Ties (D : D7) (large₂ : SizeData₂ D) (Cn : ℝ) : Type 1 where
  X : TermTie D
  Y : ∀ u u' : D.what₂.Word, LoopTie D large₂ X u u' Cn

def Adm1 (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (a : AdmC) : Prop :=
  adm2 D large₂ h ∧ ArchimedeanSignatureMatching D large₂ h ∧ adm5 D a.CNG ∧ TelescopingFormStatement D a.Ch a.Cg a.Cb ∧ ConjugateSelfDualCharacter D a.secondBesselConstant ∧
    TheoremBWeightedBound D a.Aw a.Ch a.Cgw a.Cbw ∧ adm8 D large₂ h a.CM a.Ce ∧ adm9 D large₂ h a.C1 a.cL

def Adm2 (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (a : AdmC) : Prop :=
  adm2 D large₂ h ∧ adm5 D a.CNG ∧ TelescopingFormStatement D a.Ch a.Cg a.Cb ∧ ConjugateSelfDualCharacter D a.secondBesselConstant ∧
    TheoremBWeightedBound D a.Aw a.Ch a.Cgw a.Cbw ∧ adm8 D large₂ h a.CM a.Ce

def admitted (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (a : AdmC) : Prop :=
  Adm1 D large₂ h a ∧ adm1 D ∧ adm3 D large₂ h ∧ adm6 D a.Ch a.Cg a.Cb

def IntegralityFromMetric (D : D7) (large₂ : SizeData₂ D) {Cn : ℝ} (_ : Ties D large₂ Cn) (h : LargenessConstants) (a : AdmC) (c C : ℝ) : Prop :=
  Adm1 D large₂ h a → Conclusion1 D large₂ h c C

def HodgeTateFromSandwich (D : D7) (large₂ : SizeData₂ D) {Cn : ℝ} (_ : Ties D large₂ Cn) (h : LargenessConstants) (a : AdmC) (C : ℝ) : Prop :=
  Adm2 D large₂ h a → Conclusion2 D large₂ h C

def Stmt (D : D7) (large₂ : SizeData₂ D) {Cn : ℝ} (_ : Ties D large₂ Cn) (h : LargenessConstants) (a : AdmC) (c C C2 : ℝ) : Prop :=
  admitted D large₂ h a → Conclusion1 D large₂ h c C ∧ Conclusion2 D large₂ h C2

structure Given where
  C0 : ℝ
  Cg : ℝ
  cb : ℝ
  Cu : ℝ
  cT : ℝ
  CT : ℝ
  one_le_window_constant : 1 ≤ C0
  cb_pos : 0 < cb
  cT_pos : 0 < cT

def Given.wth (g : Given) (C' Cl : ℝ) : LargenessConstants := ⟨g.C0, C', Cl, g.Cg, g.cb, g.Cu, g.cT, g.CT⟩

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (g : Given)

def admF1 : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i)
def admF2 : Prop := OwnEv Fm fun C' Cl x i => adm2 (Fm.D x i) (Fm.L x i) (g.wth C' Cl)
def admF3 : Prop := OwnEv Fm fun C' Cl x i => adm3 (Fm.D x i) (Fm.L x i) (g.wth C' Cl)
def admF4 : Prop := OwnEv Fm fun C' Cl x i => ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) (g.wth C' Cl)
def admF5 (C : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i) C
def admF6 (Ch Cg Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i) Ch Cg Cb
def FamilyWeightedBoundFirst (Ch Cg Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), TelescopingFormStatement (Fm.D x i) Ch Cg Cb
def FamilyWeightedBoundSecond (C : ℝ) : Prop := ∀ x (i : Fm.Ix x), ConjugateSelfDualCharacter (Fm.D x i) C
def FamilyWeightedBoundThird (Aw Ch Cg Cb : ℝ) : Prop := ∀ x (i : Fm.Ix x), TheoremBWeightedBound (Fm.D x i) Aw Ch Cg Cb
def admF8 (C Ce : ℝ) : Prop := OwnEv Fm fun C' Cl x i => adm8 (Fm.D x i) (Fm.L x i) (g.wth C' Cl) C Ce

def admF9 (c : ℝ) : Prop := OwnEv Fm fun C' Cl x i => adm9 (Fm.D x i) (Fm.L x i) (g.wth C' Cl) Cl c

def FirstFiltrationHypotheses (a : AdmC) : Prop :=
  admF2 Fm g ∧ admF4 Fm g ∧ admF5 Fm a.CNG ∧ FamilyWeightedBoundFirst Fm a.Ch a.Cg a.Cb ∧ FamilyWeightedBoundSecond Fm a.secondBesselConstant ∧
    FamilyWeightedBoundThird Fm a.Aw a.Ch a.Cgw a.Cbw ∧ admF8 Fm g a.CM a.Ce ∧ admF9 Fm g a.cL

def SecondFiltrationHypotheses (a : AdmC) : Prop :=
  admF2 Fm g ∧ admF5 Fm a.CNG ∧ FamilyWeightedBoundFirst Fm a.Ch a.Cg a.Cb ∧ FamilyWeightedBoundSecond Fm a.secondBesselConstant ∧
    FamilyWeightedBoundThird Fm a.Aw a.Ch a.Cgw a.Cbw ∧ admF8 Fm g a.CM a.Ce

def ConclusionF1 (c C : ℝ) : Prop := OwnEv Fm fun C' Cl x i => Conclusion1 (Fm.D x i) (Fm.L x i) (g.wth C' Cl) c C

def ConclusionF2 (C : ℝ) : Prop := OwnEv Fm fun C' Cl x i => Conclusion2 (Fm.D x i) (Fm.L x i) (g.wth C' Cl) C

def PeriodFamilyStatement (a : AdmC) (c C : ℝ) : Prop :=
  FirstFiltrationHypotheses Fm g a → ConclusionF1 Fm g c C

def DeterminantValueFamily (a : AdmC) (C : ℝ) : Prop :=
  SecondFiltrationHypotheses Fm g a → ConclusionF2 Fm g C

end Fam

def UniformClosedFormStatement (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ (g : Given) (CNG secondBesselConstant CM Ce cL : ℝ), 0 < cL → ∃ Aw Ch : ℝ, ∀ Cg Cb Cgw Cbw : ℝ, ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧
    Formalism.MainNotions.Closed 𝒞 fun Fm _ =>
      PeriodFamilyStatement Fm g ⟨CNG, Ch, Cg, Cb, secondBesselConstant, Aw, Cgw, Cbw, CM, Ce, 0, cL⟩ c C

def ClosedFormProjectorBound (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ (g : Given) (CNG secondBesselConstant CM Ce : ℝ), ∃ Aw Ch : ℝ, ∀ Cg Cb Cgw Cbw : ℝ, ∃ C : ℝ, 0 ≤ C ∧
    Formalism.MainNotions.Closed 𝒞 fun Fm _ =>
      DeterminantValueFamily Fm g ⟨CNG, Ch, Cg, Cb, secondBesselConstant, Aw, Cgw, Cbw, CM, Ce, 0, 0⟩ C

def UniformClosedFormFunctions (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ (g : List ℝ → Given) (CNG secondBesselConstant CM Ce cL : List ℝ → ℝ), (∀ l, 0 < cL l) → ∃ Aw Ch : List ℝ → ℝ,
    ∀ Cg Cb Cgw Cbw : List ℝ → ℝ, ∃ c C : List ℝ → ℝ, (∀ l, 0 < c l ∧ 0 ≤ C l) ∧
    Formalism.MainNotions.Closed 𝒞 fun Fm _ =>
      PeriodFamilyStatement Fm (g Fm.cOut) ⟨CNG Fm.cOut, Ch Fm.cOut, Cg Fm.cOut, Cb Fm.cOut, secondBesselConstant Fm.cOut, Aw Fm.cOut, Cgw Fm.cOut,
        Cbw Fm.cOut, CM Fm.cOut, Ce Fm.cOut, 0, cL Fm.cOut⟩ (c Fm.cOut) (C Fm.cOut)

def UniformClosedFormSecond (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∀ (g : List ℝ → Given) (CNG secondBesselConstant CM Ce : List ℝ → ℝ), ∃ Aw Ch : List ℝ → ℝ,
    ∀ Cg Cb Cgw Cbw : List ℝ → ℝ, ∃ C : List ℝ → ℝ, (∀ l, 0 ≤ C l) ∧
    Formalism.MainNotions.Closed 𝒞 fun Fm _ =>
      DeterminantValueFamily Fm (g Fm.cOut) ⟨CNG Fm.cOut, Ch Fm.cOut, Cg Fm.cOut, Cb Fm.cOut, secondBesselConstant Fm.cOut, Aw Fm.cOut, Cgw Fm.cOut,
        Cbw Fm.cOut, CM Fm.cOut, Ce Fm.cOut, 0, 0⟩ (C Fm.cOut)

end Formalism.MainNotions.UniformConstantsAndStatements

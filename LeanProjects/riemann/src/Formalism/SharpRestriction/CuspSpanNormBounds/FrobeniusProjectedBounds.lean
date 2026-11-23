import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic

noncomputable section

namespace Formalism.MainNotions.FrobeniusProjectedBounds

open Formalism.BasicNotions Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Letters

variable (D : D7)

def kR : ℝ := D.R.k

def mR : ℝ := D.R.m

def fR : ℝ := D.R.f

def rR : ℝ := D.R.rS

def nR : ℝ := D.R.r

def du (u : D.what₂.Word) : ℝ := D.duS u

def Dall : ℝ := D.what₂.Dall

def Dst : ℝ := D.what₂.Dstar

def Gam : ℝ := (D.mem D.u₀).A.GamP

end Letters

section Flags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def SameFlag {T T' : E} (F : Lat.LFlag S r T) (F' : Lat.LFlag S r T') : Prop :=
  (∀ j, Lat.Xflag F' j = Lat.Xflag F j) ∧ Lat.Xplus F' = Lat.Xplus F

end Flags

section Parts

variable (D : D7)

def Kpp (u u' : D.what₂.Word) : D.s.Cu u' →L[ℂ] D.s.Cu u :=
  KOf D.s u u' {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}

def scalG {D : D7} {u u' : D.what₂.Word} (p : D.s.Pair u u') : Prop :=
  p ∈ pairsIn D.s (famG D.s) ∧ scalarP D.s p

end Parts

def Hyp (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ StandingNumericalData D C0 ∧ 1 ≤ C0

def GamC {D : D7} (large₂ : SizeData₂ D) (cL cN CN CE c7 : ℝ) : Prop :=
  0 < cL ∧ 0 < cN ∧ 0 ≤ CN ∧ 0 ≤ CE ∧ 0 < c7 ∧ max CE CN + 1 ≤ large₂.CGam

def GamB {D : D7} (large₂ : SizeData₂ D) (cL cN CN CE : ℝ) : Prop :=
  0 < cL ∧ 0 < cN ∧ 0 ≤ CN ∧ 0 ≤ CE ∧ max CE CN + 1 ≤ large₂.CGam

section Statements

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 : ℝ)

def adm1 : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ u u' : D.what₂.Word, KExpansion D.s u u' ∧ KAbsConv D.s u u'

def adm2 : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (u u' : D.what₂.Word) (Φ : Set (D.s.Term u u')), IsSat D Φ → (∀ t ∈ Φ, D.s.Gterm t ≠ 0) →
    Summable (fun p : pairsIn D.s Φ => ‖D.s.pval p.1‖) →
    hsNormSq (KOf D.s u u' Φ) ≤
      (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) * gaG D *
        (∑' p : pairsIn D.s Φ, D.s.pval p.1).re

def adm3 : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ u : D.what₂.Word, hsNormSq (Kpp D u u) ≤ du D u * Real.exp (-(kR D * fR D * Real.log (kR D)))

def ArchimedeanSignatureMatching (c : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (u u' : D.what₂.Word) (S : Finset (D.s.Pair u u')), (∀ p ∈ S, loopP D.s p) →
    gaG D * ∑ p ∈ S, ‖D.s.pval p‖ ≤
      Real.exp (-(c * kR D * fR D * Real.log (kR D))) * (du D u * du D u') / Dst D

def adm5 (c C : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ u u' : D.what₂.Word, hsNormSq (KOf D.s u u' (famNG D.s)) ≤
    (Real.exp (-(c * kR D * fR D * Real.log (kR D))) +
      (2 : ℝ) ^ (-(kR D - 2 * rR D - 5)) * Real.exp (C * mR D ^ 5 * fR D * large₂.sc.L)) *
      (du D u * du D u') / Dst D

def adm6 (C : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ u : D.what₂.Word,
    Summable (fun p : {p : D.s.Pair u u // scalG p} => D.s.pval p.1) ∧
    ‖(gaG D : ℂ) * ∑' p : {p : D.s.Pair u u // scalG p}, D.s.pval p.1‖ ≤
      Real.exp (C * mR D ^ 5 * fR D * large₂.sc.L) * du D u ^ 2 / Dst D

def adm7 (c : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  |Dall D - Dst D| ≤ Real.exp (-(c * nR D * fR D * Real.log (nR D))) * Dst D

def adm8 : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), ¬ D.s.relevant t → D.s.aTerm u u' t = 0

def adm9 : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u : D.what₂.Word, IdCellDiag D.s u

def adm10 : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 → Lat.Dr1 (X.fl t) (X.fl' t) ≠ 0

def AdmA : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm8 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm9 D large₂ C' Cl Cg cb Cu cT CT C0 ∧
    adm10 D large₂ X C' Cl Cg cb Cu cT CT C0

def admitted (cL cN CN CE c7 : ℝ) : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm2 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm3 D large₂ C' Cl Cg cb Cu cT CT C0 ∧
    ArchimedeanSignatureMatching D large₂ C' Cl Cg cb Cu cT CT C0 cL ∧ adm5 D large₂ C' Cl Cg cb Cu cT CT C0 cN CN ∧
    adm6 D large₂ C' Cl Cg cb Cu cT CT C0 CE ∧ adm7 D large₂ C' Cl Cg cb Cu cT CT C0 c7 ∧
    adm8 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm9 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm10 D large₂ X C' Cl Cg cb Cu cT CT C0

def Conclusion1 : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u : D.what₂.Word,
  HasSum (fun t : {t : D.s.Term u u // D.s.inS t} => D.s.aTerm u u t.1) (ContinuousLinearMap.id ℂ (D.s.Cu u)) ∧
  (∀ t : D.s.Term u u, D.s.isId t → D.s.inS t) ∧
  (∀ t : D.s.Term u u, D.s.inS t → D.s.relevant t → D.s.isId t) ∧
  (∀ t : D.s.Term u u, SameFlag (X.fl t) (X.fl' t) → D.s.relevant t → D.s.isId t) ∧
  (∀ t : D.s.Term u u, ¬ D.s.relevant t → D.s.aTerm u u t = 0) ∧
  (∀ t : D.s.Term u u, D.s.inS t → D.s.Gterm t = 0) ∧
  KOf D.s u u {t | D.s.relevant t ∧ D.s.Gterm t = 0 ∧ ¬ SameFlag (X.fl t) (X.fl' t)} = Kpp D u u ∧
  (∀ p : D.s.Pair u u, D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → 1 ≤ D.s.s0 p)

def Conclusion2 : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u : D.what₂.Word,
  hsNormSq (Kmat D.s u u - Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) ≤ Gam D * du D u ^ 2 / Dst D

def aux₃ : Prop := Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0 ∧ Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0

def IntegralityGoodReduction : Prop := AdmA D large₂ X C' Cl Cg cb Cu cT CT C0 → Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0

def SecondFromFirstStatement (cL cN CN CE c7 : ℝ) : Prop :=
  GamC large₂ cL cN CN CE c7 → admitted D large₂ X C' Cl Cg cb Cu cT CT C0 cL cN CN CE c7 →
    Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0 → Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0

def Stmt (cL cN CN CE c7 : ℝ) : Prop :=
  GamC large₂ cL cN CN CE c7 → admitted D large₂ X C' Cl Cg cb Cu cT CT C0 cL cN CN CE c7 →
    aux₃ D large₂ X C' Cl Cg cb Cu cT CT C0

def MramC (u : D.what₂.Word) : Submodule ℂ (D.s.Cu u) :=
  ((D.mem u).A.Mram).comap (((D.mem u).A.Mu0.subtype).comp (D.s_Cu u).toLinearMap)

def FixAt (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    Submodule ℂ ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
  (D.mem u).A.Mu0 ⊓ ⨅ c : ((D.mem u).A.Fv v)ˣ, LinearMap.ker ((D.mem u).A.rhoT v c - LinearMap.id)

def adm11 : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (u : D.what₂.Word) (v : (D.mem u).A.vT), (Module.finrank ℂ (FixAt D u v) : ℝ) = du D u / (Tr D u - 1)

def AdmC : Prop :=
  adm3 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm11 D large₂ C' Cl Cg cb Cu cT CT C0

def eF (D : D7) (C0 : ℝ) : ℝ := 2 * C0 / Gam D + 2 * Real.exp (-(kR D * fR D * Real.log (kR D)))

def PointsLemma : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  (∀ u : D.what₂.Word, hsDiagAllD D u ≤ eF D C0 * du D u) ∧
  (∀ u : D.what₂.Word, du D u - (Module.finrank ℂ (MramC D u) : ℝ) ≤ 2 * fR D * du D u / Tr D u)

def PropositionCStatement : Prop := AdmC D large₂ C' Cl Cg cb Cu cT CT C0 → PointsLemma D large₂ C' Cl Cg cb Cu cT CT C0

def Adm1 : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm8 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm9 D large₂ C' Cl Cg cb Cu cT CT C0

def IntegralityFromMetric : Prop := Adm1 D large₂ C' Cl Cg cb Cu cT CT C0 → Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0

def Adm2 (cL cN CN CE : ℝ) : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm2 D large₂ C' Cl Cg cb Cu cT CT C0 ∧
    ArchimedeanSignatureMatching D large₂ C' Cl Cg cb Cu cT CT C0 cL ∧ adm5 D large₂ C' Cl Cg cb Cu cT CT C0 cN CN ∧
    adm6 D large₂ C' Cl Cg cb Cu cT CT C0 CE

def HodgeTateFromSandwich (cL cN CN CE : ℝ) : Prop :=
  GamB large₂ cL cN CN CE → Adm2 D large₂ C' Cl Cg cb Cu cT CT C0 cL cN CN CE →
    Conclusion1 D large₂ X C' Cl Cg cb Cu cT CT C0 → Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0

def LatticeChainWithoutLast : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ u : D.what₂.Word, hsDiagAllD D u ≤ eF D C0 * du D u

def ProjectedHilbertSchmidtBound : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ (Pi : ∀ u, D.s.Cu u →L[ℂ] D.s.Cu u), (∀ u, IsOrthProjOnto (Pi u) (MramC D u)) →
    (∀ Ws : Finset D.what₂.Word,
      ∑ u ∈ Ws, hsNormSq ((Pi u).comp ((Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u)).comp (Pi u)))
        ≤ eF D C0 * ∑ u ∈ Ws, du D u) ∧
    (∀ (u : D.what₂.Word) (PiH : D.s.HH →L[ℂ] D.s.HH) (SH : Submodule ℂ D.s.HH), IsOrthProjOnto PiH SH →
      ((Pi u).comp ((Kmat D.s u u).comp (Pi u)) -
        (((c0 D.s u)⁻¹ : ℝ) : ℂ) • ((Pi u).comp ((ContinuousLinearMap.adjoint (D.s.Pu u)).comp
          (PiH.comp ((D.s.Pu u).comp (Pi u)))))).IsPositive)

def CoveringRadiusFunction : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ u : D.what₂.Word, du D u - (Module.finrank ℂ (MramC D u) : ℝ) ≤ 2 * fR D * du D u / Tr D u

def ConditionalUnprojectedFrobeniusBound : Prop :=
  adm3 D large₂ C' Cl Cg cb Cu cT CT C0 → Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 → LatticeChainWithoutLast D large₂ C' Cl Cg cb Cu cT CT C0

def CoveringRadiusFromTransference : Prop := adm11 D large₂ C' Cl Cg cb Cu cT CT C0 → CoveringRadiusFunction D large₂ C' Cl Cg cb Cu cT CT C0

end Statements

section LinAlg

variable {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

theorem hsNormSq_eq (A : H →L[ℂ] G) : hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ H i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (A (stdOrthonormalBasis ℂ H i))

end LinAlg

theorem weightConst_nonneg (D : D7) (u : D.what₂.Word) : 0 ≤ c0 D.s u := by
  unfold c0 dimPi
  refine div_nonneg (mul_nonneg ?_ ?_) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
  · exact (D.s.volN_pos u).le
  · exact (D.s.volH_pos u).le

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Cg cb Cu cT CT C0 : ℝ)

def admF1 : Prop := OwnEv Fm fun C' Cl x i => adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def admF2 : Prop := OwnEv Fm fun C' Cl x i => adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def admF3 : Prop := OwnEv Fm fun C' Cl x i => adm3 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def admF4 (c : ℝ) : Prop := OwnEv Fm fun C' Cl x i => ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 c
def admF5 (c C : ℝ) : Prop := OwnEv Fm fun C' Cl x i => adm5 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 c C
def admF6 (C : ℝ) : Prop := OwnEv Fm fun C' Cl x i => adm6 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C
def admF7 (c : ℝ) : Prop := OwnEv Fm fun C' Cl x i => adm7 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 c
def admF8 : Prop := OwnEv Fm fun C' Cl x i => adm8 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def admF9 : Prop := OwnEv Fm fun C' Cl x i => adm9 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def FamilyRowsCountHypothesis : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, adm10 (Fm.D x i) (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0
def FamilyWeylAndVandermonde : Prop := OwnEv Fm fun C' Cl x i => adm11 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def GamCF (cL cN CN CE c7 : ℝ) : Prop :=
  0 < cL ∧ 0 < cN ∧ 0 ≤ CN ∧ 0 ≤ CE ∧ 0 < c7 ∧ max CE CN + 1 ≤ Fm.CGam

def AdmAF : Prop :=
  admF1 Fm Cg cb Cu cT CT C0 ∧ admF8 Fm Cg cb Cu cT CT C0 ∧ admF9 Fm Cg cb Cu cT CT C0 ∧
    FamilyRowsCountHypothesis Fm At Cg cb Cu cT CT C0

def AdmF (cL cN CN CE c7 : ℝ) : Prop :=
  admF1 Fm Cg cb Cu cT CT C0 ∧ admF2 Fm Cg cb Cu cT CT C0 ∧ admF3 Fm Cg cb Cu cT CT C0 ∧
    admF4 Fm Cg cb Cu cT CT C0 cL ∧ admF5 Fm Cg cb Cu cT CT C0 cN CN ∧
    admF6 Fm Cg cb Cu cT CT C0 CE ∧ admF7 Fm Cg cb Cu cT CT C0 c7 ∧
    admF8 Fm Cg cb Cu cT CT C0 ∧ admF9 Fm Cg cb Cu cT CT C0 ∧ FamilyRowsCountHypothesis Fm At Cg cb Cu cT CT C0

def ConclusionF1 : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ hx : Fm.x1 < x, Conclusion1 (Fm.D x i) (Fm.L x i) (At x hx i) C' Cl Cg cb Cu cT CT C0
def ConclusionF2 : Prop := OwnEv Fm fun C' Cl x i => Conclusion2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def ConclusionF3 : Prop := OwnEv Fm fun C' Cl x i => PointsLemma (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def AdmCF : Prop :=
  admF3 Fm Cg cb Cu cT CT C0 ∧ ConclusionF2 Fm Cg cb Cu cT CT C0 ∧ FamilyWeylAndVandermonde Fm Cg cb Cu cT CT C0

def OrbitValuationBound : Prop := ConclusionF1 Fm At Cg cb Cu cT CT C0 ∧ ConclusionF2 Fm Cg cb Cu cT CT C0

def DivisionSideFamily : Prop := AdmAF Fm At Cg cb Cu cT CT C0 → ConclusionF1 Fm At Cg cb Cu cT CT C0

def FamilySecondFromFirst (cL cN CN CE c7 : ℝ) : Prop :=
  GamCF Fm cL cN CN CE c7 → AdmF Fm At Cg cb Cu cT CT C0 cL cN CN CE c7 →
    ConclusionF1 Fm At Cg cb Cu cT CT C0 → ConclusionF2 Fm Cg cb Cu cT CT C0

def KudlaFamilyStatement (cL cN CN CE c7 : ℝ) : Prop :=
  GamCF Fm cL cN CN CE c7 → AdmF Fm At Cg cb Cu cT CT C0 cL cN CN CE c7 →
    OrbitValuationBound Fm At Cg cb Cu cT CT C0

def PropositionCFamily : Prop := AdmCF Fm Cg cb Cu cT CT C0 → ConclusionF3 Fm Cg cb Cu cT CT C0

def GamBF (cL cN CN CE : ℝ) : Prop :=
  0 < cL ∧ 0 < cN ∧ 0 ≤ CN ∧ 0 ≤ CE ∧ max CE CN + 1 ≤ Fm.CGam

def FamilyUnprojectedFrobenius : Prop := OwnEv Fm fun C' Cl x i => LatticeChainWithoutLast (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0
def FamilyFixedSubspaceCodimBound : Prop := OwnEv Fm fun C' Cl x i => CoveringRadiusFunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def FamilyProjectedFrobenius : Prop := OwnEv Fm fun C' Cl x i => ProjectedHilbertSchmidtBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def FamilyGlobalDerivation : Prop :=
  admF1 Fm Cg cb Cu cT CT C0 ∧ admF8 Fm Cg cb Cu cT CT C0 ∧ admF9 Fm Cg cb Cu cT CT C0 →
    ConclusionF1 Fm At Cg cb Cu cT CT C0

def SecondPartFamily (cL cN CN CE : ℝ) : Prop :=
  GamBF Fm cL cN CN CE →
    admF1 Fm Cg cb Cu cT CT C0 ∧ admF2 Fm Cg cb Cu cT CT C0 ∧ admF4 Fm Cg cb Cu cT CT C0 cL ∧
      admF5 Fm Cg cb Cu cT CT C0 cN CN ∧ admF6 Fm Cg cb Cu cT CT C0 CE →
    ConclusionF1 Fm At Cg cb Cu cT CT C0 → ConclusionF2 Fm Cg cb Cu cT CT C0

def ConditionalFamilyUnprojectedFrobenius : Prop :=
  admF3 Fm Cg cb Cu cT CT C0 → ConclusionF2 Fm Cg cb Cu cT CT C0 → FamilyUnprojectedFrobenius Fm Cg cb Cu cT CT C0

def FamilyFixedRankStatement : Prop := FamilyWeylAndVandermonde Fm Cg cb Cu cT CT C0 → FamilyFixedSubspaceCodimBound Fm Cg cb Cu cT CT C0

end Family

end Formalism.MainNotions.FrobeniusProjectedBounds

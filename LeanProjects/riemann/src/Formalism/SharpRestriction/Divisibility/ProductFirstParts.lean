import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open MvPolynomial Filter Topology Finset

namespace Formalism.MainNotions.product_first_partition

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

open Formalism.MainNotions.WeightThresholdDefs (dE dimY jS inSmall Dominant gap supAbs WeightHyp bigB0 geoDeg NefHT NefDR)

open Classical

section Derived
variable {D : D7} (Y : ShimX D.what₂.Tau)

def badPr : Finset ℕ := Nat.primeFactors (2 * dE D) ∪ Y.lev

def latSet (B : ℝ) : Finset ℕ := (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime ∪ badPr Y

def PBR (B R : ℝ) (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ :=
  Y.arDeg (latSet Y B) R (linRoot lam ^ (dimY Y + 1))

def PB (B : ℝ) (lam : D.what₂.Tau → Fin Y.N → ℝ) : ℝ := limUnder atTop (fun R => PBR Y B R lam)

def castW (u : D.what₂.Tau → Fin Y.N → ℚ) : D.what₂.Tau → Fin Y.N → ℝ := fun τ i => (u τ i : ℝ)

def slFun (B : ℝ) (u : D.what₂.Tau → Fin Y.N → ℝ) (c : Y.Comp) (s : ℚ) : ℝ :=
  Y.arSelfC (Y.Mbar B u s) c / (((dimY Y : ℝ) + 1) * Y.geoC (Y.Mbar B u s) c)

def degH (p : ℕ) (c : Y.CurveDR p) : EmbC D → ℝ
  | Sum.inl τ => ∑ i : Fin Y.N, Y.degDR p c (τ, i)
  | Sum.inr τ => -∑ i : Fin Y.N, Y.degDR p c (τ, i)

end Derived

section admitted
variable (D : D7) (L : SizeData₂ D) (V : DivX D) (P : DIV.Align.PrinLev V)

def adm1 : Prop := WeightThresholdDefs.NefHodgeTateLattices V P

def adm2 : Prop := WeightThresholdDefs.TrivialFlagIntersectionCond V P

def adm3 (C1 : ℝ) : Prop := WeightThresholdDefs.LogarithmicExponentBound V P C1

def ArchimedeanSignatureMatching : Prop := WeightThresholdDefs.ExponentBlockSplitting V P

def adm5 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → LatticeTransfer.adm1 D V S κ

def adm6 : Prop := WeightThresholdDefs.Conclusion2 V P

def adm7 : Prop := LatticeTransfer.PointsLemma D V P

def adm8 : Prop := LatticeTransfer.Conclusion4 D V P

def adm9 (r0 : ℝ) : Prop := WeightThresholdDefs.Conclusion4 V r0

def adm10 (C5 : ℝ) : Prop := WeightThresholdDefs.Conclusion5 V P C5

def adm11 : Prop := (∀ S κ, HidaSetting D V S κ →
  (∃ C : ℝ, ∀ z, (V.shv S κ).rfn z ^ (-C) ≤ (V.shv S κ).hLo z ∧
    (V.shv S κ).hUp z ≤ (V.shv S κ).rfn z ^ C ∧ (V.shv S κ).connN z ≤ C ∧
    (V.shv S κ).curvN z ≤ C) ∧
  0 < (V.shv S κ).vol) ∧ WeightThresholdDefs.adm10 V

def adm12 (CF : ℝ) : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ →
  (∀ τ z z', (V.shv S κ).compOf z = (V.shv S κ).compOf z' →
    (V.shv S κ).normDetInf τ z = (V.shv S κ).normDetInf τ z') ∧
  (∀ p : ℕ, p.Prime → ∀ τ y y', (V.shv S κ).compPt y = (V.shv S κ).compPt y' →
    (V.shv S κ).normDetT p τ y = (V.shv S κ).normDetT p τ y' ∧
    (V.shv S κ).normDetH p τ y = (V.shv S κ).normDetH p τ y') ∧
  ∀ u g, WeightHyp (V.shv S κ) u g → ∀ (B : ℝ), bigB0 (V.shv S κ) u g ≤ B →
    ((badPr (V.shv S κ)).card : ℝ) ≤ B → ∀ c τ, |(V.shv S κ).htDetT B c τ| ≤
    CF * (V.shv S κ).N * (Real.log (B * D.host.rdE) + |L.logDerivativeAtOne|)

def adm13 (C2 : ℝ) : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime →
  ∀ (y : (V.shv S κ).Pt) (lam : D.what₂.Tau → Fin (V.shv S κ).N → ℝ),
    |∑ x : Rt D.what₂.Tau (V.shv S κ).N, lam x.1 x.2 * (V.shv S κ).phiFr p y x| ≤
      C2 * Real.log p * ∑ τ, (∑ i, |lam τ i|) * (1 / ((p : ℝ) - 1) + 2 * V.vdd p τ)

def adm14 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ Lb : (V.shv S κ).ALB,
  ((V.shv S κ).semipos Lb → (V.shv S κ).arNef Lb →
      (V.shv S κ).arVol Lb = (V.shv S κ).arSelf Lb) ∧
  ((V.shv S κ).semipos Lb → (V.shv S κ).nefFib Lb →
      (V.shv S κ).arSelf Lb ≤ (V.shv S κ).arVol Lb)

def ArithmeticDegreeLeVolume : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ Lb : (V.shv S κ).ALB,
  (V.shv S κ).semipos Lb → (V.shv S κ).arNef Lb → (V.shv S κ).arSelf Lb ≤ (V.shv S κ).arVol Lb

def ArithmeticDegreeGeVolume : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ Lb : (V.shv S κ).ALB,
  (V.shv S κ).semipos Lb → (V.shv S κ).arNef Lb → (V.shv S κ).arVol Lb ≤ (V.shv S κ).arSelf Lb

def FibreNefVolumeBound : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ Lb : (V.shv S κ).ALB,
  (V.shv S κ).semipos Lb → (V.shv S κ).nefFib Lb → (V.shv S κ).arSelf Lb ≤ (V.shv S κ).arVol Lb

def adm15 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * dE D →
  p ∉ (V.shv S κ).lev → ∀ (c : (V.shv S κ).CurveDR p) (σ : EmbC D),
    degH (V.shv S κ) p c (frobEmb D p 1 σ) = (p : ℝ) * degH (V.shv S κ) p c σ

def adm16 : Prop := DIV.Align.FanAt D V P

def adm17 : Prop := DIV.Align.FanArAt D V P

def admitted (C1 r0 C5 CF C2 : ℝ) : Prop :=
  adm1 D V P ∧ adm2 D V P ∧ adm3 D V P C1 ∧ ArchimedeanSignatureMatching D V P ∧ adm5 D V P ∧ adm6 D V P ∧ adm7 D V P ∧ adm8 D V P ∧
  adm9 D V r0 ∧ adm10 D V P C5 ∧ adm11 D V ∧ adm12 D L V P CF ∧ adm13 D V P C2 ∧ adm14 D V P ∧ adm15 D V P ∧
  adm16 D V P ∧ adm17 D V P

end admitted

section Conclusion₂
variable (D : D7) (L : SizeData₂ D) (V : DivX D) (P : DIV.Align.PrinLev V)

def Conclusion0 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ B : ℝ,
  ∃ Q : MvPolynomial (Rt D.what₂.Tau (V.shv S κ).N) ℝ, ∀ lam : D.what₂.Tau → Fin (V.shv S κ).N → ℝ,
    Tendsto (fun R => PBR (V.shv S κ) B R lam) atTop (𝓝 (eval (fun x => lam x.1 x.2) Q))

def Conclusion1 (C : ℝ) : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ u g, WeightHyp (V.shv S κ) u g →
  ((badPr (V.shv S κ)).card : ℝ) ≤ bigB0 (V.shv S κ) u g →
  PB (V.shv S κ) (bigB0 (V.shv S κ) u g) u ≥
    -C * ((dimY (V.shv S κ) : ℝ) + 1) * geoDeg (V.shv S κ) u *
      ((Real.log (bigB0 (V.shv S κ) u g * D.host.rdE) + |L.logDerivativeAtOne|) * (∑ τ, ∑ i, |u τ i|) +
        (jS (V.shv S κ) : ℝ) * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i))

def ApproximantLimitFormula : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ (uq : D.what₂.Tau → Fin (V.shv S κ).N → ℚ) (g : ℝ),
  WeightHyp (V.shv S κ) (castW (V.shv S κ) uq) g →
  ((badPr (V.shv S κ)).card : ℝ) ≤ bigB0 (V.shv S κ) (castW (V.shv S κ) uq) g →
  Tendsto (fun s : ℚ => (V.shv S κ).arSelf ((V.shv S κ).Mbar
      (bigB0 (V.shv S κ) (castW (V.shv S κ) uq) g) (castW (V.shv S κ) uq) s))
    (𝓝[>] 0) (𝓝 (PB (V.shv S κ) (bigB0 (V.shv S κ) (castW (V.shv S κ) uq) g)
      (castW (V.shv S κ) uq))) ∧
  ∀ᶠ s : ℚ in 𝓝[>] 0,
    (V.shv S κ).semipos ((V.shv S κ).Mbar
      (bigB0 (V.shv S κ) (castW (V.shv S κ) uq) g) (castW (V.shv S κ) uq) s) ∧
    (V.shv S κ).nefFib ((V.shv S κ).Mbar
      (bigB0 (V.shv S κ) (castW (V.shv S κ) uq) g) (castW (V.shv S κ) uq) s)

def Conclusion2 : Prop := ∀ S κ, HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ (uq : D.what₂.Tau → Fin (V.shv S κ).N → ℚ) (g : ℝ),
  WeightHyp (V.shv S κ) (castW (V.shv S κ) uq) g →
  ((badPr (V.shv S κ)).card : ℝ) ≤ bigB0 (V.shv S κ) (castW (V.shv S κ) uq) g →
  (∀ c, ∃ l : ℝ, Tendsto (slFun (V.shv S κ) (bigB0 (V.shv S κ) (castW (V.shv S κ) uq) g)
      (castW (V.shv S κ) uq) c) (𝓝[>] 0) (𝓝 l)) ∧
  PB (V.shv S κ) (bigB0 (V.shv S κ) (castW (V.shv S κ) uq) g) (castW (V.shv S κ) uq) /
      (((dimY (V.shv S κ) : ℝ) + 1) * geoDeg (V.shv S κ) (castW (V.shv S κ) uq)) =
    (∑ c, limUnder (𝓝[>] (0 : ℚ)) (slFun (V.shv S κ)
        (bigB0 (V.shv S κ) (castW (V.shv S κ) uq) g) (castW (V.shv S κ) uq) c)) /
      (Fintype.card (V.shv S κ).Comp : ℝ)

def Stmt (C1 r0 C5 CF C2 C : ℝ) : Prop :=
  admitted D L V P C1 r0 C5 CF C2 → Conclusion0 D V P ∧ Conclusion1 D L V P C ∧ ApproximantLimitFormula D V P ∧ Conclusion2 D V P

end Conclusion₂

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (PL : DIV.Align.PrinLevF Fm)

def AdmF (C1 r0 C5 CF C2 : ℝ) : Prop := ∀ (x : ℝ) (hx : Fm.x1 < x)
  (i : Fm.Ix x), admitted (Fm.D x i) (Fm.L x i) (Fm.X x i) (PL x hx i) C1 r0 C5 CF C2

def DiscreteSeriesLowestKTypeFormula : Prop := ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion0 (Fm.D x i) (Fm.X x i) (PL x hx i)

def Conclusion1Family (C : ℝ) : Prop := ∀ (x : ℝ) (hx : Fm.x1 < x)
  (i : Fm.Ix x), Conclusion1 (Fm.D x i) (Fm.L x i) (Fm.X x i) (PL x hx i) C

def ApproximantsFamily : Prop := ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), ApproximantLimitFormula (Fm.D x i) (Fm.X x i) (PL x hx i)

def Conclusion2Family : Prop := ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion2 (Fm.D x i) (Fm.X x i) (PL x hx i)

def KudlaFamilyStatement (C1 r0 C5 CF C2 C : ℝ) : Prop := AdmF Fm PL C1 r0 C5 CF C2 →
  DiscreteSeriesLowestKTypeFormula Fm PL ∧ Conclusion1Family Fm PL C ∧ ApproximantsFamily Fm PL ∧ Conclusion2Family Fm PL

end Fam

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) (𝒬 : DIV.Align.PrinLevClass) : Prop := ∀ C1 r0 C5 CF C2 : ℝ, ∃ C : ℝ,
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ PL, 𝒬 Fm PL → KudlaFamilyStatement Fm PL C1 r0 C5 CF C2 C)

end Formalism.MainNotions.product_first_partition

end

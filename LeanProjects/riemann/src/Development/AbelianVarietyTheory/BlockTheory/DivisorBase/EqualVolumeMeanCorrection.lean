import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.DegreeFormula.FlagDegFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg

open Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Formalism.MainNotions.DIV.Align Filter Topology

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EqualVolumeMeanCorrection

open Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr

section One
variable {D : D7} (Y : ShimX D.what₂.Tau)

def RatWt (u : D.what₂.Tau → Fin Y.N → ℝ) : Prop := ∀ τ i, ∃ q : ℚ, u τ i = (q : ℝ)

def IsCompVol (volC : Y.Comp → ℝ) : Prop :=
  (∀ c, 0 < volC c) ∧ ∑ c, volC c = Y.vol ∧
    ∀ (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ), WeightHyp Y u g → RatWt Y u → ∀ c,
      Tendsto (fun s : ℚ => Y.geoC (Y.Mbar (bigB0 Y u g) u s) c) (𝓝[>] 0)
        (𝓝 (volC c * flagDeg D.what₂.Tau Y.N u))

def IsSlope (B : ℝ) (u : D.what₂.Tau → Fin Y.N → ℝ) (c : Y.Comp) (a : ℝ) : Prop :=
  (∀ᶠ s : ℚ in 𝓝[>] 0, 0 < Y.geoC (Y.Mbar B u s) c) ∧
    Tendsto (fun s : ℚ => Y.arSelfC (Y.Mbar B u s) c /
      (((dimY Y : ℝ) + 1) * Y.geoC (Y.Mbar B u s) c)) (𝓝[>] 0) (𝓝 a)

def meanC (a : Y.Comp → ℝ) : ℝ := (∑ c, a c) / (Fintype.card Y.Comp : ℝ)

def bracket (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) : ℝ :=
  (Real.log (bigB0 Y u g * NumberField.rootDiscr D.host.E) + |dlogL D 1|) * (∑ τ, ∑ i, |u τ i|) +
    (jS Y : ℝ) * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i)

def EqualVol : Prop := ∃ volC : Y.Comp → ℝ, IsCompVol Y volC ∧ ∀ c c', volC c = volC c'

def SlopesMean (C : ℝ) : Prop :=
  ∀ (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ), WeightHyp Y u g → RatWt Y u →
    ∃ sl : Y.Comp → ℝ, (∀ c, IsSlope Y (bigB0 Y u g) u c (sl c)) ∧
      (∃ Φ : Pol D.what₂.Tau Y.N →ₗ[ℝ] ℝ, IsLimDeg Y (bigB0 Y u g) Φ ∧ 0 < geoDeg Y u ∧
        meanC Y sl = atWt Y Φ u / (((dimY Y : ℝ) + 1) * geoDeg Y u)) ∧
      -(C * bracket Y u g) ≤ meanC Y sl

theorem IsSlope.unique {B : ℝ} {u : D.what₂.Tau → Fin Y.N → ℝ} {c : Y.Comp} {a b : ℝ}
    (ha : IsSlope Y B u c a) (hb : IsSlope Y B u c b) : a = b :=
  tendsto_nhds_unique ha.2 hb.2

end One

def CompCor (D : D7) (V : DivX D) (P : PrinLev V) (C : ℝ) : Prop :=
  ∀ (S : HS D) (κ : V.Lev), DV.HidaSetting D V S κ → LevB P κ →
    EqualVol (V.shv S κ) ∧ SlopesMean (V.shv S κ) C

def CompCorF {eps : ℝ} (Fm : FamP eps) (PL : PrinLevF Fm) (C : ℝ) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), CompCor (Fm.D x i) (Fm.X x i) (PL x hx i) C

def CompCorClosed (𝒞 : FamClass) (𝒬 : PrinLevClass) : Prop :=
  ∃ C : ℝ, Closed 𝒞 (fun Fm _ => ∀ PL, 𝒬 Fm PL → CompCorF Fm PL C)

end GlobalTheory.IndefiniteRowSideFullHecke.EqualVolumeMeanCorrection

end

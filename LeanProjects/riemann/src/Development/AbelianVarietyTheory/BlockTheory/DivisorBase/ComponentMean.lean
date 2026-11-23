import Mathlib
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLimDeg

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Formalism.MainNotions.DIV.Align Filter Topology

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean

open GlobalTheory.FlagPoly GlobalTheory.FlagAr

section One

variable {D : D7} (Y : ShimX D.what₂.Tau)

def realWt (u : D.what₂.Tau → Fin Y.N → ℚ) : D.what₂.Tau → Fin Y.N → ℝ := fun τ i => (u τ i : ℝ)

def slopeAt (B : ℝ) (u : D.what₂.Tau → Fin Y.N → ℝ) (c : Y.Comp) (s : ℚ) : ℝ :=
  Y.arSelfC (Y.Mbar B u s) c / (((dimY Y : ℝ) + 1) * Y.geoC (Y.Mbar B u s) c)

def IsSlope (B : ℝ) (u : D.what₂.Tau → Fin Y.N → ℝ) (sl : Y.Comp → ℝ) : Prop :=
  ∀ c, Tendsto (slopeAt Y B u c) (𝓝[>] (0 : ℚ)) (𝓝 (sl c))

open Classical in

def IsCompVol (w : Y.Comp → ℝ) : Prop :=
  (∀ c, 0 < w c) ∧ Y.vol = ∑ c, w c ∧
  ∀ (u : D.what₂.Tau → Fin Y.N → ℚ) (g : ℝ), WeightHyp Y (realWt Y u) g → ∀ c,
    Tendsto (fun s : ℚ => Y.geoC (Y.Mbar (bigB0 Y (realWt Y u) g) (realWt Y u) s) c) (𝓝[>] (0 : ℚ))
      (𝓝 (w c * flagDeg D.what₂.Tau Y.N (realWt Y u)))

def compMean (a : Y.Comp → ℝ) : ℝ := (∑ c, a c) / (Fintype.card Y.Comp : ℝ)

def errTerm (B : ℝ) (u : D.what₂.Tau → Fin Y.N → ℝ) : ℝ :=
  (Real.log (B * D.host.rdE) + |dlogL D 1|) * (∑ τ, ∑ i, |u τ i|) +
    (jS Y : ℝ) * ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i)

def VolEq : Prop := ∃ w : Y.Comp → ℝ, IsCompVol Y w ∧ ∀ c c', w c = w c'

def SlopeMean (C : ℝ) : Prop :=
  ∀ (u : D.what₂.Tau → Fin Y.N → ℚ) (g : ℝ), WeightHyp Y (realWt Y u) g →
    ∃ sl : Y.Comp → ℝ, IsSlope Y (bigB0 Y (realWt Y u) g) (realWt Y u) sl ∧
      (∃ Φ : Pol D.what₂.Tau Y.N →ₗ[ℝ] ℝ, IsLimDeg Y (bigB0 Y (realWt Y u) g) Φ ∧
        0 < geoDeg Y (realWt Y u) ∧
        compMean Y sl = atWt Y Φ (realWt Y u) / (((dimY Y : ℝ) + 1) * geoDeg Y (realWt Y u))) ∧
      -(C * errTerm Y (bigB0 Y (realWt Y u) g) (realWt Y u)) ≤ compMean Y sl

example (B : ℝ) (u : D.what₂.Tau → Fin Y.N → ℝ) (a b : Y.Comp → ℝ) (ha : IsSlope Y B u a) (hb : IsSlope Y B u b) :
    a = b :=
  funext fun c => tendsto_nhds_unique (ha c) (hb c)

example (t : ℝ) : compMean Y (fun _ => t) = t := by
  have h : (Fintype.card Y.Comp : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [compMean, Finset.sum_const, Finset.card_univ]

end One

def CompCor (D : D7) (V : DivX D) (P : PrinLev V) (C : ℝ) : Prop :=
  ∀ (S : HS D) (κ : V.Lev), DV.HidaSetting D V S κ → LevB P κ →
    VolEq (V.shv S κ) ∧ SlopeMean (V.shv S κ) C

def CompCorF {eps : ℝ} (Fm : FamP eps) (PL : PrinLevF Fm) (C : ℝ) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), CompCor (Fm.D x i) (Fm.X x i) (PL x hx i) C

def CompCorClosed (𝒞 : FamClass) (𝒬 : PrinLevClass) : Prop :=
  ∃ C : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ PL, 𝒬 Fm PL → CompCorF Fm PL C)

end GlobalTheory.IndefiniteRowSideFullHecke.ComponentMean

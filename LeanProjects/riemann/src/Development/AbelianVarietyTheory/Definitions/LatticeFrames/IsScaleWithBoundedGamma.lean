import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

def TrueF (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    D = I.rec7 l Z ∧ I.IsTw ∧ ∃ w : World I l Z, IdE w.S.X

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem TrueF.elim {Q : D7 → Prop}
    (h : ∀ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z),
      I.IsTw → IdE w.S.X → Q (I.rec7 l Z)) {D : D7} (hD : TrueF D) : Q D := by
  obtain ⟨B, X, I, l, Z, rfl, h1, w, hw⟩ := hD
  exact h B X I l Z w h1 hw

def BigGap (D : D7) : Prop := D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)

def CanE (D : D7) (_L _C' : ℝ) : Prop := TrueF D ∧ BigGap D

def IsScaleWithBoundedGamma (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C' ∧ 1 ≤ large₂.CGam

def StdE (D : D7) (L C' : ℝ) : Prop := CanE D L C' ∧ IsScaleWithBoundedGamma D L C'

theorem Row.mono {E E' : D7 → ℝ → ℝ → Prop} (hE : ∀ D L C', E' D L C' → E D L C') {Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop}
    (h : Row E Q) : Row E' Q := fun Cg cb Cu cT CT h1 h2 =>
  let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2
  ⟨C, a, b, hC, fun C' Cl ha hb D L u hD he hH => h C' Cl ha hb D L u hD (hE _ _ _ he) hH⟩

def RKStd : Prop := RKFam StdE

def JointEx (E : D7 → ℝ → ℝ → Prop) : Prop :=
  ∃ Cg cb Cu cT CT : ℝ, 0 < cb ∧ 0 < cT ∧ ∀ C C'₀ Cl₀ : ℝ, ∃ (C' Cl L : ℝ) (D : D7), C'₀ ≤ C' ∧ Cl₀ ≤ Cl ∧
    TrueE D ∧ E D L C' ∧ HD D L C' Cl Cg cb Cu cT CT ∧ ∀ u, RankMu D u ∧ C * mfL D L ≤ Real.log (D.mem u).A.GamP

end GlobalTheory.Core.Rk

end

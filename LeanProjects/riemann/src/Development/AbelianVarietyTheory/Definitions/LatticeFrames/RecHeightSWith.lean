import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightWith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith

noncomputable section

namespace GlobalTheory.CoreHt

open NumberField Formalism.BasicNotions Formalism.MainNotions

def HtRowsS {D : D7} (L : SizeData₂ D) (CY : ℝ) : Prop :=
  Nonempty (ParameterChoice' D L) ∧
  (Real.log D.host.rdE ≤ L.sc.L ∧ |L.logDerivativeAtOne| ≤ L.sc.L ∧ Real.log (4 * L.sc.x) ≤ L.sc.L) ∧
  (∀ i, Real.log (D.host.g i) ≤ CY * L.sc.L + 1) ∧
  (4 * (D.R.N D.R.m : ℝ) ^ 3 ≤ L.etaSz ∧ (D.R.t : ℝ) ≤ L.etaSz ∧
    (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧ (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
    ∀ t, (L.bT t : ℝ) ≤ 2 * L.sc.b') ∧
  DelNat D ∧ ThickUp L

def hRecS {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (c : ℝ) : ℝ :=
  DV.SZbP D L c u + (∑ j ∈ SizeData₂.lifts D, DV.kernelPlaceMeanBound D L c u j) +
    c * (((D.host.TT.card : ℝ) * L.sc.b' +
      (D.R.f : ℝ) * (L.Sc + (D.R.m : ℝ) * L.etaSz + (D.R.N D.R.m : ℝ)) +
      (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2) * Real.log ((D.mem u).A.T : ℝ))

def RecHeightSWith (CY c : ℝ) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (u : D.what₂.Word), OverTC D L.sc.a → HtRowsS L CY → (∀ v, IsUnit ((D.div.Nu u).X v).det) →
    GlobalTheory.Core.HtLe (D.div.Nu u) (GlobalTheory.Core.Rk.Pt D u) (GlobalTheory.Core.Rk.Psi D u) (hRecS L u c)

def RecHeightS : Prop := ∀ CY : ℝ, ∃ c : ℝ, 0 ≤ c ∧ RecHeightSWith CY c

end GlobalTheory.CoreHt

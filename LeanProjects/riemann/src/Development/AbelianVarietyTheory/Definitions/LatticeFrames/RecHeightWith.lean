import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColMatchAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
import Formalism.LocalRingCardinality.KernelPlaceMeanBound

noncomputable section

namespace GlobalTheory.CoreHt

open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mem GlobalTheory.Mem.Col2

def OverTC (D : D7) (a : ℝ) : Prop :=
  ∃ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (_ : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ColIn.JetsIn I ∧ Formalism.L2.Col.Sizes (B.primes X) B.wts a ∧ D = I.rec7 l Z

def DelNat (D : D7) : Prop := ∃ n : ℕ, D.s.Del = n

def ThickUp {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → wj D j τ ≤ L.sc.b + L.etaSz + 1

def HtRows {D : D7} (L : SizeData₂ D) : Prop :=
  Nonempty (ParameterChoice' D L) ∧ placeRankTwoOne.Sizes D L 25 ∧ DelNat D ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) ∧ ThickUp L

def hRec {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (c : ℝ) : ℝ := DV.SZbP D L c u + ∑ j ∈ SizeData₂.lifts D, DV.kernelPlaceMeanBound D L c u j

def RecHeightWith (c : ℝ) : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (u : D.what₂.Word), OverTC D L.sc.a → HtRows L → (∀ v, IsUnit ((D.div.Nu u).X v).det) →
    GlobalTheory.Core.HtLe (D.div.Nu u) (GlobalTheory.Core.Rk.Pt D u) (GlobalTheory.Core.Rk.Psi D u) (hRec L u c)

def RecHeight : Prop := ∃ c : ℝ, 0 ≤ c ∧ RecHeightWith c

end GlobalTheory.CoreHt

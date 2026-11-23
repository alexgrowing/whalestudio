import Mathlib
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalRingCardinality.DataForced
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G
open scoped BigOperators

def degPi (D : D7) (u : D.what₂.Word) (j : ℕ) : ℝ := ∑ τ : D.what₂.Tau, nuAbs D u j τ

def topSum {D : D7} (L : SizeData₂ D) : ℝ := ∑ t : D.host.TT, (L.aT t : ℝ)

open Classical in

def sizeOffTops (D : D7) (j : ℕ) : ℝ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : D.what₂.Tau => τ ∉ topsOf D.host D.eTau), wj D j τ

def degErr {D : D7} (L : SizeData₂ D) : ℝ :=
  (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + Nm D ^ 2 + (D.R.m : ℝ) * (D.R.t : ℝ) * L.etaSz) +
    (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x

def levelLoss (D : D7) (u : D.what₂.Word) : ℝ :=
  2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℝ)) + (D.R.f : ℝ) * Nm D +
    (D.host.TT.card : ℝ) * ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) / 4

open Classical in

def absSum {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (u : D.what₂.Word) (j : ℕ) (P : ℕ → Prop) : ℝ :=
  ∑ w ∈ L.supp.filter (fun w => P (D.what₂.places.resChar w)), SizeData₂.sz w |Eval L X K c u j w|

def InertSmall {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (p : ℕ) : Prop :=
  (IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n ∧ p ∉ L.gTypes ∧ p ≠ (D.mem u).A.T

def OtherPrime {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (p : ℕ) : Prop :=
  p ∉ L.gTypes ∧ p ≠ (D.mem u).A.T ∧ p ≠ D.host.d ∧ ¬ ((IsResidueClassZero D p ∨ IsSg D p) ∧ (p : ℝ) ≤ L.sc.X'' D.R.n)

structure ItemsAt {D : D7} (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) (C : ℝ) : Prop where

  deg : ∀ u, ∀ j ∈ SizeData₂.lifts D,
    |degPi D u j - (fockDeg D j : ℝ) - (topSum L + sizeOffTops D j)| ≤ C * degErr L

  pair : ∀ u, ∀ j ∈ SizeData₂.lifts D, ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i →
    vNN X i u j w + vNN X i u j (D.what₂.places.conj w) = degPi D u j

  levelEq : ∀ u, ∀ j ∈ SizeData₂.lifts D,
    ∑ w ∈ suppAt L (D.mem u).A.T, SizeData₂.sz w (Eval L X K c u j w) =
      levelLoss D u * Real.log ((D.mem u).A.T : ℝ)

  level : ∀ u, ∀ j ∈ SizeData₂.lifts D, absSum L X K c u j (fun p => p = (D.mem u).A.T) ≤ C * L.B0

  ramPlace : ∀ u, ∀ j ∈ SizeData₂.lifts D, ∀ t : HH D,
    (t ∈ D.host.TT → ctD D u j t * Real.log (D.host.d : ℝ) ≤
      2 * (L.sc.b + 2 * (D.R.k : ℝ) * L.sc.b') * Real.log (D.host.d : ℝ)) ∧
    (t ∉ D.host.TT → ctD D u j t * Real.log (D.host.d : ℝ) ≤ 4 * (D.R.k : ℝ) * L.sc.b' * Real.log (D.host.d : ℝ))

  ramAbs : ∀ u, ∀ j ∈ SizeData₂.lifts D, ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = D.host.d →
    |Eval L X K c u j w| ≤ (D.host.TT.card : ℝ) * L.sc.b + (D.R.f : ℝ) * D.R.k * L.sc.b'

  ramSum : ∀ u, ∀ j ∈ SizeData₂.lifts D,
    absSum L X K c u j (fun p => p = D.host.d) ≤
        (D.host.TT.card : ℝ) * (2 * L.sc.b + 4 * (D.R.k : ℝ) * L.sc.b') * Real.log (D.host.d : ℝ) +
          4 * (D.R.f : ℝ) * D.R.k * L.sc.b' * Real.log (D.host.d : ℝ) ∧
      absSum L X K c u j (fun p => p = D.host.d) ≤ 3 * (D.R.f : ℝ) * D.R.m * L.sc.b

  ramSize : (D.host.TT.card : ℝ) * (2 * L.sc.b + 4 * (D.R.k : ℝ) * L.sc.b') * Real.log (D.host.d : ℝ) +
    4 * (D.R.f : ℝ) * D.R.k * L.sc.b' * Real.log (D.host.d : ℝ) ≤ L.B0

  inert : ∀ u, ∀ j ∈ SizeData₂.lifts D, absSum L X K c u j (InertSmall L u) ≤ C * L.B0

  other : ∀ u, ∀ j ∈ SizeData₂.lifts D, absSum L X K c u j (OtherPrime L u) ≤ C * L.B0

  shiftLip : ∀ p : ℕ, p.Prime → (IsResidueClassZero D p ∨ IsSg D p) → (p : ℝ) ≤ L.sc.X'' D.R.n → ¬ (IsResidueClassZero D p ∧ hP D p = 0) →
    ∀ A B : ZMod (nP D p) → ℝ, (∀ s, 0 ≤ A s) → (∀ s, 0 ≤ B s) →
      |lpF p (nP D p) (fun s => A s + B s) - lpF p (nP D p) A| ≤ ∑ s, B s

  shiftSize : C * ((D.R.f : ℝ) * D.R.k * Nm D) * L.sc.X'' D.R.n ≤ L.sc.b

def ItemsWith {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    ItemsAt (Fm.L x i) (Fm.ex x hx i).errX Fm.GK Fm.cX.err C

def ItemsFam {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C : ℝ, 1 ≤ C ∧ ItemsWith Fm C

def Stmt : Prop := ∀ (eps : ℝ) (Fm : FamP eps), TuSize Fm → DGamSize Fm → ItemsFam Fm

def ShareAbsoluteConstant : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), Fm.CTu ≤ 25 → TuSize Fm → DGamSize Fm → ItemsWith Fm C

end GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

end

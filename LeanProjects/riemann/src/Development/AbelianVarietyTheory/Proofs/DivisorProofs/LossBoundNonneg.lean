import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLossDegreeBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BracketAbsoluteSums
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

namespace GlobalTheory.LossItemsCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.HCEntries

section Programme

variable {l d : ℕ} [NeZero d]

end Programme

section Point

variable {D : D7} {L : SizeData₂ D} {X : ErrX D} {K : Consts} {c : ErrC}

def OffSupp (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D, ∀ w, w ∉ L.supp → Eval L X K c u j w = 0

def TypeLossAt (L : SizeData₂ D) (X : ErrX D) (K : Consts) (c : ErrC) : Prop :=
  ∀ u, ∀ j ∈ SizeData₂.lifts D, ∀ (i : Fin 2), ∀ w ∈ PlacesAboveMainDegree.plAbove D (D.host.g i), Eval L X K c u j w =
    Fval L j w + vNN X i u j w + c.g * (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz)

def RamSizeAt (L : SizeData₂ D) : Prop :=
  (D.host.TT.card : ℝ) * (2 * L.sc.b + 4 * (D.R.k : ℝ) * L.sc.b') * Real.log (D.host.d : ℝ) +
    4 * (D.R.f : ℝ) * D.R.k * L.sc.b' * Real.log (D.host.d : ℝ) ≤ L.B0

def ShiftLipAt (L : SizeData₂ D) : Prop :=
  ∀ p : ℕ, p.Prime → (IsResidueClassZero D p ∨ IsSg D p) → (p : ℝ) ≤ L.sc.X'' D.R.n → ¬ (IsResidueClassZero D p ∧ hP D p = 0) →
    ∀ A B : ZMod (nP D p) → ℝ, (∀ s, 0 ≤ A s) → (∀ s, 0 ≤ B s) →
      |lpF p (nP D p) (fun s => A s + B s) - lpF p (nP D p) A| ≤ ∑ s, B s

def ShiftSizeAt (L : SizeData₂ D) (C : ℝ) : Prop := C * (exch D * L.sc.X'' D.R.n) ≤ L.sc.b

def TypeUnitAt (D : D7) : Prop := ∀ u (i : Fin 2), padicValNat (D.host.g i) (D.mem u).C.DGam = 0

theorem cube_le_eta (P : ParameterChoice' D L) : 4 * (D.R.N D.R.m : ℝ) ^ 3 + 6 ≤ L.etaSz := by
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have a1 := P.h0_ge.2.2.2.2.1
  have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self L.etaSz_pos.le hm
  linarith [one_le_letterBlockLength D]

end Point

section Family

variable {eps : ℝ} (Fm : FamP eps)

def ItemsWithDvd (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), PlacesAboveMainDegree.GamDvd (Fm.D x i) →
    LevelLossDegreeBounds.ItemsAt (Fm.L x i) (Fm.ex x hx i).errX Fm.GK Fm.cX.err C

def DvdFam : Prop := ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, PlacesAboveMainDegree.GamDvd (Fm.D x i)

def TypeUnitFam : Prop := ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, TypeUnitAt (Fm.D x i)

end Family

end GlobalTheory.LossItemsCompare

end

import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NkExponent
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def PairFactsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        (A : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) →
        ∀ (mu : Fin (2 * segS X.TT j + 1 + 1) → Fin (X.m + 1) → ℤ) (lam : Fin X.m → ℤ),
          IsPair A (clA C0 CE1 CE2 X j rz ry) (clC C0 CE1 CE2 X j rz ry) mu lam →
          pairC mu 0 = (A : ℤ) ∧ (∀ l, 0 ≤ pairC mu l) ∧
          (∀ i : Fin (segS X.TT j), 0 ≤ pairRho mu i ∧ pairRho mu i ≤ pairC mu i ∧
            ((pairRho mu i : ℤ) : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2) ∧
            -(4 * (clA C0 CE1 CE2 X j rz ry i : ℝ) / (X.p : ℝ) ^ 2) ≤
              ((pairO mu (clA C0 CE1 CE2 X j rz ry) i - pairRho mu i : ℤ) : ℝ)) ∧
          0 ≤ lam 0 ∧ lam 0 ≤ pairC mu (segS X.TT j) ∧
          ∀ i : Fin (segS X.TT j), 0 ≤ pairN (s := segS X.TT j) lam i ∧
            ((pairN (s := segS X.TT j) lam i : ℤ) : ℝ) ≤ (clC C0 CE1 CE2 X j rz ry i : ℝ) * (1 + 4 / (X.p : ℝ) ^ 2)

def CoarseDegreesLargeAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ A : ℕ, ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) →
        X.k ^ 3 ≤ (A : ℝ) ∧ (∀ i, X.k ^ 3 ≤ (clA C0 CE1 CE2 X j rz ry i : ℝ)) ∧
          (∀ i, X.k ^ 3 ≤ (clC C0 CE1 CE2 X j rz ry i : ℝ)) ∧ X.k ^ 2 ≤ (X.p : ℝ) ∧ 10 ≤ X.k ∧
          1 ≤ X.La C0 ∧ 4 * X.La C0 ≤ X.k

def RestPairFacts : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => PairFactsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def CoarseDegreesLargeBeyond : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => CoarseDegreesLargeAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf

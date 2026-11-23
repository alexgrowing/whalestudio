import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CoarseMultiplicityAtIdentity

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def NumCoreAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc), D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c → ∀ e : ℕ, 1 ≤ e → e < n →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j b →
      (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ (i : ℕ) →
        1 + 2 * (X.p ^ X.G' * e) + b.o i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b i) ∧
      ∀ b' : SegBlock (segS X.TT j) X.m,
        DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b' →
        (∀ i, coarseA X.p (X.seg C0 CE1 CE2 j) b i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b' i + (X.m + 1)) →
        (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ (i : ℕ) →
          b'.o i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b' i ∧ b'.o i ≤ b.o i + 2 * ((X.m + 1) + X.p ^ X.G' * e) ∧
          b'.w i = 0 ∧ b'.sg i = 0) →
        (∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
          b'.o i = 0 ∧ b'.w i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b' i ∧
          b'.sg i ≤ coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b' i ∧
          b'.sg i ≤ b.sg i + ((X.m + 1) + X.p ^ X.G' * e) ∧ b'.w i ≤ b.w i + ((X.m + 1) + X.p ^ X.G' * e)) →
        b'.oPlus ≤ segAPlus X.TT X.aT j → b'.oPlus ≤ b.oPlus + X.p ^ X.G' * e →
        BLk C0 Cde CE1 CE2 X (((X.c - (n - e) : ℕ) : ℝ) * ka1 X) j b' ∧
        ∀ (l : ℕ) (V : ℤ), V ≤ ((X.N1 : ℤ) + 1) * (((X.m : ℤ) + 1) + (X.p : ℤ) ^ X.G' * e) →
          ⌊((cap X.p (X.seg C0 CE1 CE2 j) b l : ℤ) : ℝ) - (mm + (n : ℝ) * ka1 X)⌋ + ((X.N1 * e : ℕ) : ℤ) + V ≤
            ⌊((cap X.p (X.seg C0 CE1 CE2 j) b' l : ℤ) : ℝ) - (mm + ((n - e : ℕ) : ℝ) * ka1 X)⌋

def RestNumCore : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => NumCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf

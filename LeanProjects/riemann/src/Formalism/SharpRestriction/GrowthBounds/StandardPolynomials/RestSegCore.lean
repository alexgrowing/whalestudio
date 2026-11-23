import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCoreDef
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymbolFormOfOrthogonality

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def segMon (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (A : MonH X) : RHH O X :=
  (∏ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
    (MvPolynomial.X ((topOdd X j i, true), c) ^ A ((topOdd X j i, true), c) *
      MvPolynomial.X ((topOdd X j i, false), c) ^ A ((topOdd X j i, false), c))) *
  ∏ c : Fin (X.m + 1), (MvPolynomial.X ((topEnd X j, true), c) ^ A ((topEnd X j, true), c) *
      MvPolynomial.X ((topEnd X j, false), c) ^ A ((topEnd X j, false), c))

def chW {s : ℕ} (i : Fin s) : Fin (2 * s + 1) := ⟨2 * i.val, by omega⟩
def chE {s : ℕ} (i : Fin s) : Fin (2 * s + 1) := ⟨2 * i.val + 1, by omega⟩
def chU (s : ℕ) : Fin (2 * s + 1) := ⟨2 * s, by omega⟩

def nuSeg (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ) (jp : ℕ)
    (du : Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) : ℕ :=
  (∑ i : Fin (segS X.TT j), ((X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
    (∑ c : Fin X.m, A ((topOdd X j i, true), c.succ)) + A ((topOdd X j i, false), 0))) +
  (jp + du (chU _) + ∑ c : Fin X.m, A ((topEnd X j, true), c.succ))

def SegCoreAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β),
    ∀ e : ℕ, 1 ≤ e → e < n →
    ∀ (j : Fin (numSeg X.TT)) (ju : Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ), (∀ i, ju i ≤ L.lv j i) →
    ∀ (Gu : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) (du : Fin (2 * segS X.TT j + 1) → ℕ),
      Gu ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m) →
      Gu ∈ Pol (KK O) X.m du → (∀ a, du a ≤ (L.LL j).deg a) →
      (∀ k, Gu ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
        ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k + (((X.N1 * e : ℕ) : ℤ) : WithTop ℤ))) →
    ∀ A : MonH X,

      (∀ i : Fin (segS X.TT j), (β j).rz i 0 + (X.seg C0 CE1 CE2 j).P X.p i *
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
            (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) ≤
          A ((topOdd X j i, true), 0) + X.p ^ X.G' * e) →
      (∀ i : Fin (segS X.TT j), ∑ c : Fin X.m, (A ((topOdd X j i, true), c.succ) - (β j).rz i c.succ) ≤ X.p ^ X.G' * e) →
      (∀ i : Fin (segS X.TT j), A ((topOdd X j i, false), 0) ≤ (β j).ry i 0 + (X.seg C0 CE1 CE2 j).P X.p i *
          (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) + X.p ^ X.G' * e) →
      (∑ c : Fin X.m, A ((topEnd X j, true), c.succ) ≤ X.p ^ X.G' * e) →
      A ((topEnd X j, false), 0) = 0 → (∀ c : Fin X.m, A ((topEnd X j, false), c.succ) = L.γ j c) →

      (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i)) +
        ∑ c, A ((topOdd X j i, true), c) = (X.seg C0 CE1 CE2 j).bTop i) →
      (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i * (jE (X.seg C0 CE1 CE2 j) ju i.val + du (chE i)) +
        ∑ c, A ((topOdd X j i, false), c) = segATop X.TT X.aT j i) →
      (L.jp j + du (chU _) + ∑ c, A ((topEnd X j, true), c) = segAPlus X.TT X.aT j) →
      ∃ b' : SegBlock (segS X.TT j) X.m,
        BLk C0 Cde CE1 CE2 X (((X.c - (n - e) : ℕ) : ℝ) * ka1 X) j b' ∧
        blockOrd X.p (X.seg C0 CE1 CE2 j) b' = nuSeg C0 CE1 CE2 X j ju (L.jp j) du A ∧
        ∃ u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
            (mm + ((n - e : ℕ) : ℝ) * ka1 X) b').SSZ O (r := X.m),
          L.head O j ju Gu * segMon O X j A = ioBlock (KK O) X.p C0 CE1 CE2 X j b' u

def RestSegCore : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SegCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf

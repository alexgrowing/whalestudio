import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.PreSys

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

structure ColSys (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O) (mu : ℝ) (β : GlobalTheory X)
    (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) where
  ι : Type
  fin : Fintype ι
  Kc : ι → MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)
  dK : ι → Fin (2 * segS X.TT j + 1) → ℕ
  pl : ι → MonH X
  fC : ι → RHH O X
  oC : ι → ℕ
  dgC : ι → X.TT × Bool → ℕ
  a0 : ℕ
  KInt : ∀ a, Kc a ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)
  KPol : ∀ a, Kc a ∈ Pol (KK O) X.m (dK a)
  digit_le_one : ∀ a i, dK a i ≤ 1
  dKsum : ∀ i, ∑ a, dK a i = (L.LL j).deg i
  Kprod : ∏ a, Kc a = G
  facC : ∀ a, IsFac w (fC a) (oC a)
    (monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)))
  homC : ∀ a, HomW (ndHom X) (oC a)
    (monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)))
  fPol : ∀ a, fC a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC a)
  polC : ∀ a, monomial (pl a) 1 * ioD O C0 CE1 CE2 mu X β j (rename (chainEmb _ X.m _) (Kc a)) ∈
    Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgC a)
  plQ : ∀ a l, multideg (pl a) l ≤ X.p ^ X.G'
  dgCQ : ∀ a l, dgC a l ≤ X.p ^ X.G'
  dgCY : ∀ a j', dgC a (topEnd X j', false) = 0
  a0le : (a0 : ℤ) + ∑ i : Fin (segS X.TT j), (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg i : ℤ) else 0) ≤
    (X.seg C0 CE1 CE2 j).A0 X.p
  plSum : ∑ a, pl a = Finsupp.single ((topStart X j, true), 0) ((X.seg C0 CE1 CE2 j).Qj X.p * a0) +
    ∑ i : Fin (segS X.TT j), Finsupp.single ((topOdd X j i, true), 0)
      ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
        (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)))
  oSum : ∑ a, oC a = (∑ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).P X.p i *
      (L.LL j).deg ⟨2 * (i : ℕ), by have := i.2; omega⟩) + (L.LL j).deg ⟨2 * segS X.TT j, by omega⟩

def ColsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β) (j : Fin (numSeg X.TT)) (y : Tx X.m (L.LL j)),
      y ∈ sAll (L.LL j) (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr →
      Nonempty (ColSys C0 CE1 CE2 X O S.w (mm + (n : ℝ) * ka1 X) β L j (psiR (KK O) (L.LL j) y))

def RestCols : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => ColsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf

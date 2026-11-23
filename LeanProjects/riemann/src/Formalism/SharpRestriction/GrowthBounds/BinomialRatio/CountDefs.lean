import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankDefs

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

def Strip {r : ℕ} (nu mu : Fin r → ℤ) (g : ℕ) : Prop :=
  (∀ i, mu i ≤ nu i) ∧ (∀ i j : Fin r, i.val + 1 = j.val → nu j ≤ mu i) ∧ ∑ i, nu i - ∑ i, mu i = (g : ℤ)

def wdim {r : ℕ} (lam : Fin r → ℤ) : ℚ :=
  ∏ i : Fin r, ∏ j : Fin r, if i < j then ((lam i : ℚ) - (lam j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1

def IsChain {N r : ℕ} (LL : ChainLetters N) (ka : Fin (N + 1) → Fin r → ℤ) : Prop :=
  ka 0 = 0 ∧ ∀ i : Fin N, if LL.vec i then Strip (ka i.succ) (ka i.castSucc) (LL.deg i)
    else Strip (ka i.castSucc) (ka i.succ) (LL.deg i)

def ChainOK {N r : ℕ} [NeZero r] {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ka : Fin (N + 1) → Fin r → ℤ) : Prop :=
  ∀ k, ((ka (finPos N (J k)) 0 : ℤ) : WithTop ℤ) ≤ M k

open Classical in

def chainSum {N r : ℕ} [NeZero r] (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) : ℚ :=
  ∑ᶠ ka : Fin (N + 1) → Fin r → ℤ, if IsChain LL ka ∧ ChainOK J M ka then wdim (ka (Fin.last N)) else 0

def sdXi (r g : ℕ) : ℕ := Nat.choose (g + r - 1) (r - 1)

open Classical in

def BlockRankAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N r : ℕ) [NeZero r] (D : BlockData N),
    Module.finrank (KK O) (Submodule.span (KK O)
        ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
          Set (MvPolynomial (BVar N r D.T.t) (KK O)))) =
      ∑ᶠ x : (Fin D.T.t → ℕ) × ℕ, if D.LevelOK x.1 x.2 then
        Module.finrank (KK O) (Yjt (KK O) (r := r) (D.lettersAt x.1 x.2) D.T.J D.T.thr) * sdXi r (D.B - x.2) else 0

def DimYAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O)
    (N r : ℕ) [NeZero r] (LL : ChainLetters N) (q : ℕ) (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ), (∀ k, J k ≤ N) →
    (Module.finrank (KK O) (Yjt (KK O) (r := r) LL J M) : ℚ) = chainSum (r := r) LL J M

def StWeylAt : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B),
    (Nat.card {I : ℤ → Finset (Fin n) // IsSt P.mu I} : ℚ) = wdim (pEnd P.mu)

open Classical in

def NumBranchAt : Prop :=
  ∀ (r : ℕ) (mu : Fin (r + 1) → ℤ), Antitone mu →
    wdim mu = ∑ᶠ lam : Fin r → ℤ, if (∀ i : Fin r, mu i.succ ≤ lam i ∧ lam i ≤ mu i.castSucc) then wdim lam else 0

def ChainDimAt : Prop :=
  ∀ (N r : ℕ) [NeZero r] (LL : ChainLetters N),
    chainSum (r := r) LL (q := 0) Fin.elim0 Fin.elim0 = ∏ i, (sdXi r (LL.deg i) : ℚ)

open Classical in

def chainCount (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (m : ℝ)
    (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) : ℚ :=
  ∑ᶠ b : SegBlock (segS X.TT j) X.m,
    if Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ∧ b.rz = rz ∧ b.ry = ry then
      (let D := blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b
       ∑ᶠ x : (Fin D.T.t → ℕ) × ℕ, if D.LevelOK x.1 x.2 then
        chainSum (r := X.m) (D.lettersAt x.1 x.2) D.T.J D.T.thr * (sdXi X.m (D.B - x.2) : ℚ) else 0)
    else 0

def CountUpAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      chainCount C0 CE1 CE2 X j m rz ry ≤ (mmB C0 CE1 CE2 X j rz ry : ℚ)

def CountLowAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      lowFac C0 CE1 CE2 X j ⌈m⌉₊ * (mmB C0 CE1 CE2 X j rz ry : ℝ) ≤ ((chainCount C0 CE1 CE2 X j m rz ry : ℚ) : ℝ)

def RestCountUp : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => CountUpAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc
def RestCountLow : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => CountLowAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf

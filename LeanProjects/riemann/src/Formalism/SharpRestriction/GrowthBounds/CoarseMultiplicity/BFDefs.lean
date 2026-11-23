import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockFG
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.MapFloorMono
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DegSplit

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev BV (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :=
  BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t

abbrev bD (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (mm : ℝ) (b : SegBlock (segS X.TT j) X.m) :
    BlockData (2 * segS X.TT j + 1) :=
  blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm b

abbrev sszB (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (mm : ℝ)
    (b : SegBlock (segS X.TT j) X.m) : Submodule O (MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) :=
  (bD C0 CE1 CE2 X j mm b).SSZ O (r := X.m)

def baseExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ :=
  (∑ i : Fin (segS X.TT j), ∑ c : Fin (X.m + 1),
    (Finsupp.single ((topOdd X j i, true), c) (b.rz i c) + Finsupp.single ((topOdd X j i, false), c) (b.ry i c))) +
  ∑ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
    Finsupp.single ((topOdd X j i, true), (0 : Fin (X.m + 1)))
        ((X.seg C0 CE1 CE2 j).P X.p i * (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i)) +
      Finsupp.single ((topOdd X j i, false), (0 : Fin (X.m + 1))) ((X.seg C0 CE1 CE2 j).P X.p i * b.sg i)
  else 0

def ioExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (μ : BV C0 CE1 CE2 X j →₀ ℕ) : ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ :=
  baseExp C0 CE1 CE2 X j b +
    μ.sum fun v n => Finsupp.single (symVar C0 CE1 CE2 X j v) (symLev X.p C0 CE1 CE2 X j v * n)

def gOp {O : Type} [CommRing O] [IsDomain O] {σ : Type} (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O)
    (u : MvPolynomial σ (KK O)) : MvPolynomial σ (KK O) :=
  ∑ ν ∈ T, q ν • (monomial ν (1 : KK O) * divDer ν u)

def gEv {O : Type} [CommRing O] {σ : Type} (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O) (μ : σ →₀ ℕ) : O :=
  ∑ ν ∈ T, q ν * ((ν.prod fun k i => (μ k).choose i : ℕ) : O)

def Balanced {s : ℕ} (r : ℕ) (S : SegData s) (ω : BVar (2 * s + 1) r S.t → ℕ) (ωL : Fin (2 * s + 1 + 1) → ℕ) : Prop :=
  (∀ a c, ω (Sum.inl (a, c)) = ωL a) ∧
  (∀ l : Fin S.t, ω (Sum.inr (Fin.castSucc l, false)) + ω (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1))) ∧
  ω (Sum.inr (Fin.last S.t, false)) + ω (Sum.inr (Fin.last S.t, true)) =
      ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)

def HomExp (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (μ : BV C0 CE1 CE2 X j →₀ ℕ) : Prop :=
  ∀ (ω : BV C0 CE1 CE2 X j → ℕ) (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ), Balanced X.m (X.seg C0 CE1 CE2 j) ω ωL →
    ∑ v, μ v * ω v = OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b ω ωL

def letterOf (X : Loc) (j : Fin (numSeg X.TT)) (a : Fin (2 * segS X.TT j + 1 + 1)) : X.TT × Bool :=
  if h : (a : ℕ) < 2 * segS X.TT j then (topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0))
  else (topEnd X j, decide ((a : ℕ) = 2 * segS X.TT j))

open Classical in

def lamW (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (x : X.TT × Bool) : BV C0 CE1 CE2 X j → ℕ :=
  fun v => if (symVar C0 CE1 CE2 X j v).1 = x then 1 else 0

open Classical in
def lamL (X : Loc) (j : Fin (numSeg X.TT)) (x : X.TT × Bool) : Fin (2 * segS X.TT j + 1 + 1) → ℕ :=
  fun a => if letterOf X j a = x then 1 else 0

def cdeg (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) (x : X.TT × Bool) : ℕ :=
  OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b (lamW C0 CE1 CE2 X j x) (lamL X j x)

def Nblk (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) : ℕ :=
  (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial) * specConst X.p (X.seg C0 CE1 CE2 j) b

def IsOddVar (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) : BV C0 CE1 CE2 X j → Prop
  | Sum.inl (a, _) => (a : ℕ) < 2 * segS X.TT j
  | Sum.inr (l, _) => (l : ℕ) < (X.seg C0 CE1 CE2 j).t

def IoFockAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) (K : Type) [Field K], 0 < X.p → ∀ (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u u' : MvPolynomial (BV C0 CE1 CE2 X j) K),
    fock (ioBlock K X.p C0 CE1 CE2 X j b u) (ioBlock K X.p C0 CE1 CE2 X j b u') =
      ∑ μ ∈ u.support, u.coeff μ * u'.coeff μ * (expFact (ioExp C0 CE1 CE2 X j b μ) : K)

def EigAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) (T : Finset (σ →₀ ℕ)) (q : (σ →₀ ℕ) → O)
    (u : MvPolynomial σ (KK O)) (μ : σ →₀ ℕ),
    (gOp T q u).coeff μ = algebraMap O (KK O) (gEv T q μ) * u.coeff μ

def HomAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b → ∀ (mm : ℝ),
      ∀ u ∈ Submodule.span (KK O) (sszB O C0 CE1 CE2 X j mm b : Set (MvPolynomial (BV C0 CE1 CE2 X j) (KK O))),
      ∀ μ ∈ u.support, HomExp C0 CE1 CE2 X j b μ

def DvdAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
    Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
    ∀ μ, HomExp C0 CE1 CE2 X j b μ → expFact μ * specConst X.p (X.seg C0 CE1 CE2 j) b ∣ Nblk C0 CE1 CE2 X j b

def SatAt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N r : ℕ) [NeZero r] (D : BlockData N),
    ∀ x ∈ Submodule.span (KK O) ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
        Set (MvPolynomial (BVar N r D.T.t) (KK O))),
      x ∈ IntPol O (BVar N r D.T.t) → x ∈ D.SSZ O (r := r)

def GThetaAt : Prop :=
  ∀ (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero (KK O)] (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
    Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
    ∀ (c : ℕ) (T : Finset (BV C0 CE1 CE2 X j →₀ ℕ)) (q : (BV C0 CE1 CE2 X j →₀ ℕ) → O),
      (∀ ν ∈ T, (ν.sum fun _ n => n) ≤ 4 * c ∧ ∀ v ∈ ν.support, IsOddVar C0 CE1 CE2 X j v) →
      ∀ (mm : ℝ), ∀ u ∈ sszB O C0 CE1 CE2 X j mm b, gOp T q u ∈ sszB O C0 CE1 CE2 X j (mm - 4 * (c : ℝ)) b

def FactAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (w : O),
    Irreducible w → w ^ 2 = (X.p : O) → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∃ (κ : O) (T : Finset (BV C0 CE1 CE2 X j →₀ ℕ)) (q : (BV C0 CE1 CE2 X j →₀ ℕ) → O),
        κ ≠ 0 ∧ vLEO X.p κ (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ∧
        (∀ ν ∈ T, (ν.sum fun _ n => n) ≤ 4 * X.c ∧ ∀ v ∈ ν.support, IsOddVar C0 CE1 CE2 X j v) ∧
        ∀ μ, HomExp C0 CE1 CE2 X j b μ → ∃ h : O,
          zSeg (KK O) X j * (X.p : KK O) ^ padicValNat X.p (Nblk C0 CE1 CE2 X j b) *
              (expFact (ioExp C0 CE1 CE2 X j b μ) : KK O) * algebraMap O (KK O) (gEv T q μ) =
            algebraMap O (KK O) κ * ((expFact μ : KK O) * (specConst X.p (X.seg C0 CE1 CE2 j) b : KK O)) *
              algebraMap O (KK O) (1 + w ^ X.c * h)

end Formalism.MainNotions.ColumnSystems.Pf

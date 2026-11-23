import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColGen

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def ioA (K : Type) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K →ₐ[K]
      MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^
      symLev p C0 CE1 CE2 X j v)

theorem ioBlock_eq (K : Type) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    ioBlock K p C0 CE1 CE2 X j b u =
      digitMon K C0 CE1 CE2 X j b * sTopMon K p C0 CE1 CE2 X j b * ioA K p C0 CE1 CE2 X j u := rfl

abbrev BDk (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) : BlockData (2 * segS X.TT j + 1) :=
  blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mu (β j)

def ioD (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT)) :
    MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O) →ₐ[KK O] RHH O X :=
  ioA (KK O) X.p C0 CE1 CE2 X j

structure LvDat (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) where
  lv : ∀ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t → ℕ
  jp : Fin (numSeg X.TT) → ℕ
  ok : ∀ j, (BDk C0 CE1 CE2 mu X β j).LevelOK (lv j) (jp j)
  γ : Fin (numSeg X.TT) → Fin X.m → ℕ
  hγ : ∀ j, ∑ c, γ j c = (BDk C0 CE1 CE2 mu X β j).B - jp j

section

variable (O : Type) [CommRing O] [IsDomain O] {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

abbrev LvDat.LL (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : ChainLetters (2 * segS X.TT j + 1) :=
  (BDk C0 CE1 CE2 mu X β j).lettersAt (L.lv j) (L.jp j)

def LvDat.stdPoly (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT)) : RHH O X :=
  digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) *
    ioD O C0 CE1 CE2 mu X β j
      ((∏ i, MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t (Fin.castSucc i)) ^
          (BDk C0 CE1 CE2 mu X β j).T.z i) *
        MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
          (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t)) ^ (BDk C0 CE1 CE2 mu X β j).zPlus *
        ∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c) ^ L.γ j c)

def LvDat.head (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (ju : Fin (BDk C0 CE1 CE2 mu X β j).T.t → ℕ) (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) : RHH O X :=
  ioD O C0 CE1 CE2 mu X β j
    ((∏ i, (BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i ^ ju i) * (BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m) ^ L.jp j *
      rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) G)

def LvDat.word (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) :
    MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O) :=
  (∏ i, (BDk C0 CE1 CE2 mu X β j).Ehat O (r := X.m) i ^ L.lv j i) * (BDk C0 CE1 CE2 mu X β j).Eplus O (r := X.m) ^ L.jp j *
      (∏ i, MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t (Fin.castSucc i)) ^
          (BDk C0 CE1 CE2 mu X β j).T.z i) *
      MvPolynomial.X (scalZ (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t
          (Fin.last (BDk C0 CE1 CE2 mu X β j).T.t)) ^ (BDk C0 CE1 CE2 mu X β j).zPlus *
      rename (chainEmb (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) G *
      ∏ c, MvPolynomial.X (xiVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t c) ^ L.γ j c

theorem LvDat.ioBlock_word (L : LvDat C0 CE1 CE2 mu X β) (j : Fin (numSeg X.TT))
    (G : MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)) :
    ioBlock (KK O) X.p C0 CE1 CE2 X j (β j) (L.word O j G) = L.head O j (L.lv j) G * L.stdPoly O j := by
  change digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) *
    ioA (KK O) X.p C0 CE1 CE2 X j (L.word O j G) = _
  simp only [LvDat.word, LvDat.head, LvDat.stdPoly, ioD]
  conv_rhs => rw [mul_comm, mul_assoc]
  erw [← map_mul]
  refine congrArg (fun w => digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) *
    ioA (KK O) X.p C0 CE1 CE2 X j w) ?_
  have hcomm : ∀ (e ep z zp r xi : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m
      (X.seg C0 CE1 CE2 j).t) (KK O)), e * ep * z * zp * r * xi = z * zp * xi * (e * ep * r) :=
    fun e ep z zp r xi => by ring
  exact hcomm _ _ _ _ _ _

end

def TCoreAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ (L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β) (Std : MonH X),
      (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j →
    ∀ e : ℕ, 1 ≤ e → e < n →
    ∀ (ju : ∀ j, Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ), (∀ j i, ju j i ≤ L.lv j i) →
    ∀ (Gu : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O))
      (du : ∀ j, Fin (2 * segS X.TT j + 1) → ℕ),
      (∀ j, Gu j ∈ IntPol O (Fin (2 * segS X.TT j + 1) × Fin X.m)) →
      (∀ j, Gu j ∈ Pol (KK O) X.m (du j)) → (∀ j a, du j a ≤ (L.LL j).deg a) →
      (∀ j k, Gu j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
        ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k + (((X.N1 * e : ℕ) : ℤ) : WithTop ℤ))) →
    ∀ A : MonH X,
      (∀ l, ∑ c, (Std (l, c) - A (l, c)) ≤ X.p ^ X.G' * e) → (∀ l, ∑ c, (A (l, c) - Std (l, c)) ≤ X.p ^ X.G' * e) →
      (∀ j c, A ((topEnd X j, false), c) = Std ((topEnd X j, false), c)) →
      (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) →
      (∀ m ∈ ((∏ j, L.head O j (ju j) (Gu j)) * monomial A 1).support, ndM X m ≤ ordFam C0 CE1 CE2 X β + e) →
      (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 ∈ SSe C0 Cde CE1 CE2 X O mm n (ordFam C0 CE1 CE2 X β) e

def RestTCore : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => TCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf

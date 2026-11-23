import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def ka1 (X : Loc) : ℝ := 13 * X.k * X.N1 * X.Q

def localOrderCap (C0 : ℝ) (X : Loc) : ℝ :=
  (X.a : ℝ) / (X.p : ℝ) ^ 2 + 3 * X.b' / X.p + (X.La C0 / X.k + 4 / (X.p : ℝ) ^ 2) * (4 * (X.a : ℝ) / X.p) +
    2 * X.La C0 * X.b' / X.k

def BLk (C0 Cde CE1 CE2 : ℝ) (X : Loc) (E : ℝ) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) : Prop :=
  DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ∧
  (∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ (i : ℕ) →
    b.o i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b i ∧
    (b.o i : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 - X.de C0 Cde / 4) + E ∧
    b.w i = 0 ∧ b.sg i = 0) ∧
  (∀ i : Fin (segS X.TT j), (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
    b.o i = 0 ∧ b.w i ≤ coarseA X.p (X.seg C0 CE1 CE2 j) b i ∧
    b.sg i ≤ coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i ∧
    (b.sg i : ℝ) ≤ 2 * X.La C0 * ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) / X.k + E) ∧
  b.oPlus ≤ segAPlus X.TT X.aT j ∧ (b.oPlus : ℝ) ≤ localOrderCap C0 X + E

def genSet (O : Type) [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (D : BlockData N) :
    Set (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  ⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens O (r := r) j jp

def InGen (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 mm : ℝ) (X : Loc) [NeZero X.m] (β : GlobalTheory X)
    (s : Syms O C0 CE1 CE2 X) : Prop :=
  ∀ j, s j ∈ genSet O (r := X.m)
    (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j))

def ordFam (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) : ℕ := ∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (β j)

def SSg (O : Type) [CommRing O] [IsDomain O] (C0 Cde CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (mu E : ℝ) (o : ℕ) :
    Submodule O (MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) :=
  Submodule.span O {σ | ∃ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X E j (β j)) ∧ ordFam C0 CE1 CE2 X β ≤ o ∧
    ∃ s : Syms O C0 CE1 CE2 X, InGen O C0 CE1 CE2 mu X β s ∧ σ = symFam (KK O) X.p C0 CE1 CE2 X β s}

def IsCleanAwayFromPlane (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (o : ℕ)
    (F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) : Prop :=
  F ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) ∧
    InA (C (algebraMap O (KK O) (w ^ o)) * F) ∧
    ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
      ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 g → InWjRg X.p X.n' O w 1 (hhLetters X.TT) g' F X.c

def RawTailBody (C0 Cde CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (mm : ℝ) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) : Prop :=
    ∀ n : ℕ, 1 ≤ n → n ≤ X.c →
    ∀ β : GlobalTheory X, (∀ j, BLk C0 Cde CE1 CE2 X (((X.c - n : ℕ) : ℝ) * ka1 X) j (β j)) →
    ∀ s : Syms O C0 CE1 CE2 X, InGen O C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β s →
      ∃ (raw : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O))
        (τ : ℕ → MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)),
        IsCleanAwayFromPlane X O w g (ordFam C0 CE1 CE2 X β) raw ∧
        (∀ ε ∈ Finset.Ico 1 n, τ ε ∈ SSg O C0 Cde CE1 CE2 X (mm + ((n - ε : ℕ) : ℝ) * ka1 X)
          (((X.c - (n - ε) : ℕ) : ℝ) * ka1 X) (ordFam C0 CE1 CE2 X β + ε)) ∧
        InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) g raw - symFam (KK O) X.p C0 CE1 CE2 X β s -
          ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • τ ε) n

def RawTailAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
      RawTailBody C0 Cde CE1 CE2 X O S.w mm g

def RawTailAt1 (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) → RawTailBody C0 Cde CE1 CE2 X O S.w mm 1

def RestRawTail1 : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => RawTailAt1 C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def CoarseMultiplicityAtIdentity (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm) (β j)).SSZ O (r := X.m)) →
      ∃ F ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT),
        InA (C (algebraMap O (KK O) (S.w ^ (∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (β j)))) * F) ∧
        InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) 1 F - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c ∧
        ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
          ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 1 → InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g' F X.c

def RestRawTail : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => RawTailAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def KeptBLAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc), D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b → BLk C0 Cde CE1 CE2 X 0 j b

def RestKeptBL : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => KeptBLAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

end Formalism.MainNotions.ColumnSystems.Pf

import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairLift
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def topOdd (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT :=
  ⟨segPos X.TT j i, (pos_mem X.TT j i).1⟩

def topEnd (X : Loc) (j : Fin (numSeg X.TT)) : X.TT :=
  ⟨segNext X.TT j, (next_mem X.TT j).1⟩

def symVar (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → (X.TT × Bool) × Fin (X.m + 1)
  | Sum.inl (a, c) =>
    if h : (a : ℕ) < 2 * segS X.TT j then
      ((topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0)), c.succ)
    else ((topEnd X j, decide ((a : ℕ) = 2 * segS X.TT j)), c.succ)
  | Sum.inr (l, b) =>
    if h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t then
      ((topOdd X j (uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩), !b), 0)
    else ((topEnd X j, !b), 0)

def symLev (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT)) :
    BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ
  | Sum.inl (a, _) =>
    if h : (a : ℕ) < 2 * segS X.TT j then (X.seg C0 CE1 CE2 j).P p ⟨(a : ℕ) / 2, by omega⟩ else 1
  | Sum.inr (l, _) =>
    if h : (l : ℕ) < (X.seg C0 CE1 CE2 j).t then (X.seg C0 CE1 CE2 j).P p (uTop (X.seg C0 CE1 CE2 j) ⟨l, h⟩) else 1

def digitMon (K : Type*) [CommSemiring K] (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ i : Fin (segS X.TT j), ∏ c : Fin (X.m + 1),
    MvPolynomial.X ((topOdd X j i, true), c) ^ b.rz i c * MvPolynomial.X ((topOdd X j i, false), c) ^ b.ry i c

def sTopMon (K : Type*) [CommSemiring K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ i : Fin (segS X.TT j), if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
    MvPolynomial.X ((topOdd X j i, true), 0) ^ ((X.seg C0 CE1 CE2 j).P p i * (coarseA p (X.seg C0 CE1 CE2 j) b i - b.w i)) *
      MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P p i * b.sg i)
  else 1

def ioBlock (K : Type*) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  digitMon K C0 CE1 CE2 X j b * sTopMon K p C0 CE1 CE2 X j b *
    aeval (fun v => (MvPolynomial.X (symVar C0 CE1 CE2 X j v) : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K) ^
      symLev p C0 CE1 CE2 X j v) u

def symFam (K : Type*) [CommRing K] (p : ℕ) (C0 CE1 CE2 : ℝ) (X : Loc)
    (β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) K) :
    MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) K :=
  ∏ j, ioBlock K p C0 CE1 CE2 X j (β j) (s j)

def Lemma44At (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ mm : ℝ, (mm = 0 ∨ mm = 12 * (X.c : ℝ)) →
    ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm) (β j)).SSZ O (r := X.m)) →
      ∃ F ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT),
        InA (C (algebraMap O (KK O) (S.w ^ (∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (β j)))) * F) ∧
        InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c ∧
        ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
          ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 g → InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g' F X.c

def BinomialRatioBeyondThreshold : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => Lemma44At C0 CYb Cde Ck CD Cb CE1 CE2 Cc

def IsFlatTheta {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O) (φ : WF p n' ≃+* W) {m : ℕ} (TT : Finset (Fin n'))
    (aT bT : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT)) : Prop :=
  letI : Algebra (WF p n') O := algOfIdent jO φ
  (∀ F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O),
      InA (O := O) (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) ↔
      Θ F ∈ HHL (O := O) ι σ TT aT bT (colSpan W h)) ∧
    (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
      ∀ e : Edge W Qq (m + 1), IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose) →
        ∀ (F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O)) (i : ℕ),
          InWjRg p n' O w 1 (hhLetters TT) g (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) i ↔
          Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (ReHH p ι σ w TT aT bT e)) ∧
    ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e → e.src = colSpan W h →
      ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g ∧ IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose)

def SrcHalfAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] [Fact X.p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → 1 ≤ X.c →
    ∀ φ : WF X.p X.n' ≃+* W, IsWittIdent σ φ →
    ∀ (h : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) Qq) Θ, IsFlatTheta ι σ jO w φ X.TT X.aT X.bT h Θ →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e → e.src = colSpan W h →
    ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
      IsEdgeBasis X.p 1 e (h * ((matQ φ g)⁻¹).transpose) →
    ∀ β : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j)) →
    ∀ s : ∀ j : Fin (numSeg X.TT), MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O),
      (∀ j, s j ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (X.m0 Cm) (β j)).SSZ O (r := X.m)) →
      ∃ F, Θ F ∈ CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e ∧
        (letI : Algebra (WF X.p X.n') O := algOfIdent jO φ
         InWj w (liftSubst X.p X.n' O w 1 (hhLetters X.TT) g
           (F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c)

end Formalism.MainNotions.ColumnSystems.Pf

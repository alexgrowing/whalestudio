import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.ObjSeg
import Formalism.SharpRestriction.GrowthBounds.ObjBridge
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.ConclusionA2

noncomputable section

namespace Formalism.MainNotions.ColumnSystems

open Formalism.MainNotions.G

structure Loc where
  p : ℕ
  n' : ℕ
  m : ℕ
  TT : Finset (Fin n')
  aT : Fin n' → ℕ
  bT : Fin n' → ℕ
  a : ℕ
  b' : ℝ
  Y : ℝ
  Yb : ℝ
  N1 : ℕ
  G' : ℕ
  bl : ℝ
  bh : ℝ
  ccl : ℝ
  DLP : ℝ
  cs : ℝ
  c : ℕ

namespace Loc

variable (X : Loc)

def k : ℝ := (X.m : ℝ) + 1

def N : ℝ := (X.TT.card : ℝ)

def Q : ℝ := (X.p : ℝ) ^ X.G'

def La (C0 : ℝ) : ℝ := lambdaScale C0 X.N1 X.a

def de (C0 Cde : ℝ) : ℝ := Cde * X.N1 * X.La C0 / X.k + 2 * (X.bh - X.bl) / X.b'

def E0 (C0 CE1 CE2 : ℝ) : ℝ := errorTermBound CE1 CE2 X.p X.k X.N1 X.Q X.c X.a X.b' (X.La C0)

def m0 (Cm : ℝ) : ℝ := m0G4 Cm X.k X.N1 X.Q X.c

def kap0 : ℝ := kap0G4 X.N X.k X.p X.a

def kapP (C0 CE1 CE2 Cm Ckap : ℝ) : ℝ :=
  kappaMarginBound Ckap X.N X.k X.Q (X.m0 Cm) X.N1 X.b' X.Y (X.E0 C0 CE1 CE2) X.a (X.La C0)

def t0 (C0 Ct : ℝ) : ℝ := t0G4 Ct X.p (X.m + 1) X.TT X.aT X.bT X.a X.b' (X.La C0) X.Q X.c

def seg (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT)) : SegData (segS X.TT j) :=
  segData X.p X.TT X.bT X.a X.b' X.Y (X.La C0) (X.E0 C0 CE1 CE2) j

end Loc

def D1num (X : Loc) : Prop := X.p.Prime ∧ 5 ≤ X.p ∧ 2 ≤ X.n' ∧ Even X.n'

def HI (C0 CYb Cde Ck CD Cb : ℝ) (X : Loc) : Prop :=
  1 ≤ X.Y ∧ X.k ^ 2 * X.Y ^ 2 ≤ (X.p : ℝ) ∧
  (∃ s ∈ X.TT, Even s.val) ∧ 2 ≤ numSeg X.TT ∧
  (∀ j, segG X.TT j ≤ X.G' ∧ segS X.TT j ≤ X.N1) ∧ 1 ≤ X.N1 ∧
  2 * X.N1 + 2 ≤ X.m ∧
  8 * Real.log (X.N * X.Y) ≤ X.La C0 ∧
  (∀ s ∈ X.TT, (X.a : ℝ) ≤ X.aT s ∧ (X.aT s : ℝ) ≤ X.a + X.a / (X.k * X.Y)) ∧
  0 < X.b' ∧ X.bl ≤ X.b' ∧ X.b' ≤ X.bh ∧
  X.Yb * X.N * X.La C0 * X.b' / X.k ≤ X.bh - X.bl ∧ X.bh - X.bl ≤ X.b' / 2 ∧
  CYb ≤ X.Yb ∧ 2 * X.Yb * X.N * X.La C0 < X.k ∧
  X.k * X.Y ^ 2 * X.Yb * X.N * X.La C0 * Real.log X.a ≤ X.a / X.b' ∧
  (∀ s ∈ X.TT, X.bl ≤ X.bT s ∧ (X.bT s : ℝ) ≤ X.bh) ∧
  X.de C0 Cde < 1 / 6 ∧ (X.p : ℝ) < X.a / X.b' ∧ Ck * X.N * X.La C0 ^ 2 ≤ X.k ∧
  (∀ d : ℕ, Odd d → ¬ ((X.a / X.b') * (1 - 2 * X.de C0 Cde) ≤ (X.p : ℝ) ^ d ∧
      (X.p : ℝ) ^ d ≤ (X.a / X.b') * (1 + 2 * X.de C0 Cde))) ∧
  0 ≤ X.ccl ∧ X.ccl ≤ X.La C0 * X.b' / X.k ∧
  CD * X.N * X.Y ^ 2 * ((X.N1 : ℝ) ^ 5 + X.k ^ 3) * Real.logb X.p X.a ≤ X.DLP ∧ 8 * (X.DLP + 1) ≤ X.cs ∧
  Cb * X.k ^ 3 * X.N * X.Q ^ 4 * (X.cs + X.N * X.ccl + X.n' * X.ccl) * X.Y ≤ X.b'

def CBound (Cc : ℝ) (X : Loc) : Prop :=
  (X.c : ℝ) ≤ Cc * (X.cs + X.N * X.k * Real.logb X.p X.a + X.N * X.ccl + X.n' * X.ccl)

def DjHyp (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (C0 CE1 CE2 Cm : ℝ) (X : Loc)
    [NeZero X.m] (Dj kT : Fin (numSeg X.TT) → ℝ) : Prop :=
  ∀ j, 0 ≤ Dj j ∧ 0 ≤ kT j ∧ GoodShare X.p (segForm O X.p X.m (X.seg C0 CE1 CE2 j))
    (segLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm)) (Dj j) (kT j)

def aux₃ (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HI C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ Dj kT : Fin (numSeg X.TT) → ℝ, DjHyp O C0 CE1 CE2 Cm X Dj kT →
    4 * ((∑ j, Dj j) + 4 * X.kap0) < (X.c : ℝ) →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e →
      RhoGE X.p (beHH (m := X.m) X.p X.TT X.aT X.bT)
        (CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e) (CCe' X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e)
        ((∑ j, Dj j) + 4 * X.kap0)
        ((1 - X.kapP C0 CE1 CE2 Cm Ckap - ∑ j, kT j) * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) /
          gaussianNumber (X.p ^ X.n') (X.m + 1))

def Conclusion2 (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs : ℝ) : Prop :=
  ∀ X : Loc, D1num X → HI C0 CYb Cde Ck CD Cb X → CBound Cc X →
    X.kapP C0 CE1 CE2 Cm Ckap ≤ Cs * X.N * X.N1 / X.Y

def PointsLemma (_D : Formalism.BasicNotions.D7) (C0 CE1 CE2 : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (j : Fin (numSeg X.TT)) (aT' : Fin X.n' → ℕ) (m : ℝ),
    segNext X.TT j ≠ segStart X.TT j → (∀ s, s ≠ segStart X.TT j → aT' s = X.aT s) →
    segLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m =
      segLat O X.p X.m (({ X with aT := aT' } : Loc).seg C0 CE1 CE2 j)
        (segATop X.TT aT' j) (segAPlus X.TT aT' j) m

def symDim (k : ℕ) (A : ℤ) : ℕ := if A < 0 then 0 else Nat.choose (A.toNat + k - 1) (k - 1)

def dimMM {s : ℕ} (k : ℕ) (A0 : ℤ) (A C : Fin s → ℕ) : ℕ :=
  symDim k A0 * ∏ i, symDim k (A i) * symDim k (C i)

def digitBlock {s r : ℕ} (rz ry : Fin s → Fin (r + 1) → ℕ) : SegBlock s r := ⟨rz, ry, 0, 0, 0, 0⟩

open Classical in

def rankOnDigits (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (C0 CE1 CE2 : ℝ) (X : Loc)
    [NeZero X.m] (j : Fin (numSeg X.TT)) (m : ℝ) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) : ℕ :=
  ∑ᶠ b : SegBlock (segS X.TT j) X.m,
    if Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ∧ b.rz = rz ∧ b.ry = ry then
      blockRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b
    else 0

def Conclusion4 (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HI C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      rankOnDigits O C0 CE1 CE2 X j 0 rz ry ≤
        dimMM (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p)
            (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
            (fun i => coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i) *
          symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).bPlus : ℤ)

def DegreeDichotomy (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HI C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∀ i : Fin (segS X.TT j),
        ((i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
          (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 + X.de C0 Cde) < ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ)) ∧
        ((X.seg C0 CE1 CE2 j).sigma ≤ (i : ℕ) →
          ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) < (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 - X.de C0 Cde))

def ModelLatticeRank (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HI C0 CYb Cde Ck CD Cb X → CBound Cc X → ∀ m : ℝ, 0 ≤ m →
      (1 - kappaMarginBound Ckap X.N X.k X.Q m X.N1 X.b' X.Y (X.E0 C0 CE1 CE2) X.a (X.La C0)) *
          (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) ≤
        gaussianNumber (X.p ^ X.n') (X.m + 1) *
          ∏ j, (segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m : ℝ)

def OrderBoundDigits (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc), D1num X → HI C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ bs : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (bs j)) →
      ((∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (bs j) : ℕ) : ℝ) ≤ X.t0 C0 Ct

def adm1 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.adm1 D

def adm2 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin (n + 1) → ℕ), Antitone lam →
    Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K (n + 1) (n + 1) lam) =
      ∑ mu ∈ (Fintype.piFinset (fun _ : Fin n => Finset.range (lam 0 + 1))).filter
          (fun mu => ∀ i : Fin n, lam i.succ ≤ mu i ∧ mu i ≤ lam i.castSucc),
        Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K n n mu)

def adm3 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (nu : Fin n → ℕ), Antitone nu →
    (Module.finrank K (Formalism.GradedWeylDivisibility.dualWeyl K n n nu) : ℚ) =
      ∏ i : Fin n, ∏ j : Fin n,
        if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1

def ArchimedeanSignatureMatching (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D

def adm5 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.AutomorphicSideConclusion D

def adm6 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D

def adm7 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.RotatedSumBound D

def adm8 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.PathWeightComponents D

def adm9 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.ConclusionB3 D

def adm10 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.CoefficientDependence D

def adm11 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.CanonicalTranslateJetIdentity D

def logVal : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ t s : ℕ, 1 ≤ s →
    Formalism.MainNotions.CovariantDegrees.PadicGe p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * ∑ y ∈ Finset.Ico 1 (p ^ (t + 1)), ((y : ℚ) ^ s)⁻¹) s ∧
    Formalism.MainNotions.CovariantDegrees.PadicGe p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * (∑ y ∈ Finset.Ico 1 (p ^ (t + 1)), ((y : ℚ) ^ s)⁻¹) / s)
      (((s : ℝ) + 1) / 4 + 1 / ((p : ℝ) - 1))

def adm12 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.UnitFunctionExpansion D ∧ logVal

def adm13 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.UnitProductSecondLemma D

def adm14 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.DerivativeLemma D

def adm15 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.HyperplaneRank D

def adm16 (_D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.G.WittIdent

def adm17 (_D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.G.FlatTop

def hhLetters {n' : ℕ} (TT : Finset (Fin n')) : LiftLetters (TT × Bool) where
  vec := fun x => x.2
  pos := fun x => (x.1.val.val : ℤ)

def hhDegs {n' : ℕ} (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : TT × Bool → ℕ :=
  fun x => hhDeg aT bT x.1.val x.2

def FlatHH : Prop :=
  ∀ (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w → ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ), 1 ≤ m →
    ∀ h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq, IsUnit h.det →
    letI : Algebra (WF p n') O := algOfIdent jO φ
    ∃ Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT),
      (∀ F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O),
        InA (O := O) (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) ↔
        Θ F ∈ HHL (O := O) ι σ TT aT bT (colSpan W h)) ∧
      (∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
        ∀ e : Edge W Qq (m + 1), IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose) →
          ∀ (F : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O)) (i : ℕ),
            InWjRg p n' O w 1 (hhLetters TT) g
              (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) i ↔
            Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (ReHH p ι σ w TT aT bT e)) ∧
      ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e → e.src = colSpan W h →
        ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g ∧
          IsEdgeBasis p 1 e (h * ((matQ φ g)⁻¹).transpose)

def adm18 (_D : Formalism.BasicNotions.D7) : Prop := FlatHH

def adm19 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.adm2 D

def adm20 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.CanonicalTranslateJetIdentity D

def admitted (D : Formalism.BasicNotions.D7) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D ∧ adm8 D ∧ adm9 D ∧ adm10 D ∧ adm11 D ∧
    adm12 D ∧ adm13 D ∧ adm14 D ∧ adm15 D ∧ adm16 D ∧ adm17 D ∧ adm18 D ∧ adm19 D ∧ adm20 D

def ExportAllConjugates (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  aux₃ D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc ∧ Conclusion2 D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs ∧
    PointsLemma D C0 CE1 CE2 ∧ Conclusion4 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc ∧ DegreeDichotomy D C0 CYb Cde Ck CD Cb CE1 CE2 Cc ∧
    ModelLatticeRank D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc ∧ OrderBoundDigits D C0 CYb Cde Ck CD Cb CE1 CE2 Ct Cc

def Stmt (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  admitted D → ExportAllConjugates D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs

def Closed (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Cc : ℝ, 0 ≤ Cc → ∃ T0 : ℝ, 0 < T0 ∧ ∀ C0 : ℝ, T0 ≤ C0 →
    ∃ T1 : ℝ, 0 < T1 ∧ ∀ CE1 CE2 Cm : ℝ, T1 ≤ CE1 → T1 ≤ CE2 → T1 ≤ Cm →
      ∃ T2 : ℝ, 0 < T2 ∧ ∀ CYb Cde Ck CD Cb : ℝ, T2 ≤ CYb → T2 ≤ Cde → T2 ≤ Ck → T2 ≤ CD → T2 ≤ Cb →
        ∃ Ckap Ct Cs : ℝ, 0 < Ckap ∧ 0 < Ct ∧ 0 < Cs ∧ P C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs

def ConclusionsWithConstants (D : Formalism.BasicNotions.D7) : Prop := Closed (Stmt D)

def ClosedFormOfAdmitted (D : Formalism.BasicNotions.D7) : Prop := admitted D → Closed (ExportAllConjugates D)

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), admitted (Fm.D x i)

def FamilyAllConclusions {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), ExportAllConjugates (Fm.D x i) C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  AdmF Fm → FamilyAllConclusions Fm C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs

def FamilyClosedForm {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → Closed (FamilyAllConclusions Fm)

def DerivativeStatementClosedDesign (Fm : Formalism.MainNotions.DFamP) : Prop :=
  (∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), AdmF (Fm ε h0 h1)) →
    Closed fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs =>
      ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), FamilyAllConclusions (Fm ε h0 h1) C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs

def Loc.J0 (X : Loc) (C0 : ℝ) : ℝ := X.La C0 * X.b' / X.k

def WindowHypotheses (C0 CYb Cde Ck CD Cb : ℝ) (X : Loc) : Prop :=
  1 ≤ X.Y ∧ X.k ^ 2 * X.Y ^ 2 ≤ (X.p : ℝ) ∧
  (∃ s ∈ X.TT, Even s.val) ∧ 2 ≤ numSeg X.TT ∧
  (∀ j, segG X.TT j ≤ X.G' ∧ segS X.TT j ≤ X.N1) ∧ 1 ≤ X.N1 ∧
  2 * X.N1 + 2 ≤ X.m ∧
  8 * Real.log (X.N * X.Y) ≤ X.La C0 ∧
  0 < X.b' ∧ X.bl ≤ X.b' ∧ X.b' ≤ X.bh ∧
  X.Yb * X.N * X.La C0 * X.b' / X.k ≤ X.bh - X.bl ∧ X.bh - X.bl ≤ X.b' / 2 ∧
  CYb ≤ X.Yb ∧ 2 * X.Yb * X.N * X.La C0 < X.k ∧
  X.k * X.Y ^ 2 * X.Yb * X.N * X.La C0 * Real.log X.a ≤ X.a / X.b' ∧
  X.de C0 Cde < 1 / 6 ∧ (X.p : ℝ) < X.a / X.b' ∧ Ck * X.N * X.La C0 ^ 2 ≤ X.k ∧
  (∀ d : ℕ, Odd d → ¬ ((X.a / X.b') * (1 - 2 * X.de C0 Cde) ≤ (X.p : ℝ) ^ d ∧
      (X.p : ℝ) ^ d ≤ (X.a / X.b') * (1 + 2 * X.de C0 Cde))) ∧
  0 ≤ X.ccl ∧ X.ccl ≤ X.La C0 * X.b' / X.k ∧
  CD * X.N * X.Y ^ 2 * ((X.N1 : ℝ) ^ 5 + X.k ^ 3) * Real.logb X.p X.a ≤ X.DLP ∧ 8 * (X.DLP + 1) ≤ X.cs ∧
  Cb * X.k ^ 3 * X.N * X.Q ^ 4 * (X.cs + X.N * X.ccl + X.n' * X.ccl) * X.Y ≤ X.b'

def InWin (xa xb : ℝ) (X : Loc) : Prop :=
  (∀ s ∈ X.TT, (X.a : ℝ) ≤ X.aT s ∧ (X.aT s : ℝ) ≤ X.a + X.a / (X.k * X.Y) + xa) ∧
  (∀ s ∈ X.TT, X.bl ≤ X.bT s ∧ (X.bT s : ℝ) ≤ X.bh + xb)

def HIext (C0 CYb Cde Ck CD Cb : ℝ) (X : Loc) : Prop :=
  WindowHypotheses C0 CYb Cde Ck CD Cb X ∧ InWin (2 * X.J0 C0) (2 * X.J0 C0) X

theorem HI_iff {C0 CYb Cde Ck CD Cb : ℝ} {X : Loc} :
    HI C0 CYb Cde Ck CD Cb X ↔ WindowHypotheses C0 CYb Cde Ck CD Cb X ∧ InWin 0 0 X := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h10, h11, h12, h13, h14, h15, h16, h17, h19, h20, h21, h22, h23, h24,
      h25, h26, h27⟩, fun s hs => ⟨(h9 s hs).1, by linarith [(h9 s hs).2]⟩,
      fun s hs => ⟨(h18 s hs).1, by linarith [(h18 s hs).2]⟩⟩
  · rintro ⟨⟨g1, g2, g3, g4, g5, g6, g7, g8, g10, g11, g12, g13, g14, g15, g16, g17, g19, g20, g21, g22, g23, g24, g25, g26, g27⟩, g9, g18⟩
    exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, fun s hs => ⟨(g9 s hs).1, by linarith [(g9 s hs).2]⟩, g10, g11, g12,
      g13, g14, g15, g16, g17, fun s hs => ⟨(g18 s hs).1, by linarith [(g18 s hs).2]⟩, g19, g20, g21, g22, g23,
      g24, g25, g26, g27⟩

theorem InWin.mono {xa xb xa' xb' : ℝ} {X : Loc} (ha : xa ≤ xa') (hb : xb ≤ xb') (h : InWin xa xb X) :
    InWin xa' xb' X :=
  ⟨fun s hs => ⟨(h.1 s hs).1, by linarith [(h.1 s hs).2]⟩, fun s hs => ⟨(h.2 s hs).1, by linarith [(h.2 s hs).2]⟩⟩

theorem WindowHypotheses.cleaning_budget_nonneg {C0 CYb Cde Ck CD Cb : ℝ} {X : Loc} (h : WindowHypotheses C0 CYb Cde Ck CD Cb X) : 0 ≤ X.J0 C0 := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g10, g11, g12, g13, g14, g15, g16, g17, g19, g20, g21, g22, g23, g24, g25, g26, g27⟩ := h
  unfold Loc.J0
  exact g23.trans g24

theorem HIext.of_le {C0 CYb Cde Ck CD Cb xa xb : ℝ} {X : Loc} (h : WindowHypotheses C0 CYb Cde Ck CD Cb X)
    (ha : xa ≤ 2 * X.J0 C0) (hb : xb ≤ 2 * X.J0 C0) (hw : InWin xa xb X) : HIext C0 CYb Cde Ck CD Cb X :=
  ⟨h, hw.mono ha hb⟩

theorem HI.toExt {C0 CYb Cde Ck CD Cb : ℝ} {X : Loc} (h : HI C0 CYb Cde Ck CD Cb X) :
    HIext C0 CYb Cde Ck CD Cb X := by
  obtain ⟨h0, hw⟩ := HI_iff.mp h
  have hJ := h0.cleaning_budget_nonneg
  exact HIext.of_le h0 (by linarith) (by linarith) hw

def HerrExtensionClass (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ Dj kT : Fin (numSeg X.TT) → ℝ, DjHyp O C0 CE1 CE2 Cm X Dj kT →
    4 * ((∑ j, Dj j) + 4 * X.kap0) < (X.c : ℝ) →
    ∀ e : Edge W Qq (X.m + 1), IsEdge X.p X.n' 1 e →
      RhoGE X.p (beHH (m := X.m) X.p X.TT X.aT X.bT)
        (CCe X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e) (CCe' X.p ι σ w X.TT X.aT X.bT ⌊X.t0 C0 Ct⌋₊ X.c e)
        ((∑ j, Dj j) + 4 * X.kap0)
        ((1 - X.kapP C0 CE1 CE2 Cm Ckap - ∑ j, kT j) * (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) /
          gaussianNumber (X.p ^ X.n') (X.m + 1))

def ExtendedKappaBound (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs : ℝ) : Prop :=
  ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    X.kapP C0 CE1 CE2 Cm Ckap ≤ Cs * X.N * X.N1 / X.Y

def ExtendedDigitRankBound (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      rankOnDigits O C0 CE1 CE2 X j 0 rz ry ≤
        dimMM (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p)
            (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
            (fun i => coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i) *
          symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).bPlus : ℤ)

def ExtendedDichotomy (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∀ i : Fin (segS X.TT j),
        ((i : ℕ) < (X.seg C0 CE1 CE2 j).sigma →
          (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 + X.de C0 Cde) < ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ)) ∧
        ((X.seg C0 CE1 CE2 j).sigma ≤ (i : ℕ) →
          ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) < (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 - X.de C0 Cde))

def ExtendedModelRank (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → ∀ m : ℝ, 0 ≤ m →
      (1 - kappaMarginBound Ckap X.N X.k X.Q m X.N1 X.b' X.Y (X.E0 C0 CE1 CE2) X.a (X.La C0)) *
          (dimHH (m := X.m) Kf X.TT X.aT X.bT : ℝ) ≤
        gaussianNumber (X.p ^ X.n') (X.m + 1) *
          ∏ j, (segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m : ℝ)

def ExtendedOrderBound (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Ct Cc : ℝ) : Prop :=
  ∀ (X : Loc), D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ bs : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m,
      (∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (bs j)) →
      ((∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (bs j) : ℕ) : ℝ) ≤ X.t0 C0 Ct

def SegmentMarginBound (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) (M : Loc → ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m] (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    UnramifiedQuadraticSetting X.p X.n' W Qq O Kf ι σ jO w → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m → m ≤ M X →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ((dimMM (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p)
            (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
            (fun i => coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i) *
          symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).bPlus : ℤ) : ℕ) : ℝ) / 2 ≤
        (rankOnDigits O C0 CE1 CE2 X j m rz ry : ℝ) ∧
      rankOnDigits O C0 CE1 CE2 X j m rz ry ≤
        dimMM (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p)
            (fun i => coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i)
            (fun i => coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i) *
          symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).bPlus : ℤ)

def RootMultiplicityTwo (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  SegmentMarginBound C0 CYb Cde Ck CD Cb CE1 CE2 Cc fun X => X.b' / (X.k * X.Q * X.Y)

def FreeTopRankBound (_D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) (aT' : Fin X.n' → ℕ), D1num X → HIext C0 CYb Cde Ck CD Cb X →
    HIext C0 CYb Cde Ck CD Cb { X with aT := aT' } → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT aT' j) b →
      (Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ↔
        Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT aT' j) b)

theorem RootMultiplicityTwo.toExtendedDigitRankBound {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (h : RootMultiplicityTwo D C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : ExtendedDigitRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hE hC j rz ry hD
  obtain ⟨⟨g1, -, -, -, -, -, -, -, g10, -⟩, -⟩ := id hE
  have hM : 0 ≤ X.b' / (X.k * X.Q * X.Y) := by
    apply div_nonneg g10.le
    apply mul_nonneg (mul_nonneg ?_ ?_) (by linarith)
    · unfold Loc.k; positivity
    · unfold Loc.Q; positivity
  exact (h X W Qq O Kf ι σ jO w hS hE hC j 0 le_rfl hM rz ry hD).2

def ExtendedAllConclusions (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  HerrExtensionClass D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc ∧ ExtendedKappaBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs ∧
    PointsLemma D C0 CE1 CE2 ∧ Conclusion4 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc ∧ ExtendedDichotomy D C0 CYb Cde Ck CD Cb CE1 CE2 Cc ∧
    ExtendedModelRank D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc ∧ ExtendedOrderBound D C0 CYb Cde Ck CD Cb CE1 CE2 Ct Cc ∧
    ExtendedDigitRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc ∧ RootMultiplicityTwo D C0 CYb Cde Ck CD Cb CE1 CE2 Cc ∧
    FreeTopRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem HerrExtensionClass.toGrowthBound {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc : ℝ}
    (h : HerrExtensionClass D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc) : aux₃ D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hHI hC
  exact h X W Qq O Kf ι σ jO w hS hHI.toExt hC

theorem ExtendedDigitRankBound.toDigitRankBound {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (h : ExtendedDigitRankBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : Conclusion4 D C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hHI hC
  exact h X W Qq O Kf ι σ jO w hS hHI.toExt hC

theorem ExtendedKappaBound.toKappaBound {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs : ℝ}
    (h : ExtendedKappaBound D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs) :
    Conclusion2 D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Cc Cs :=
  fun X hD hHI hC => h X hD hHI.toExt hC

theorem ExtendedDichotomy.toDegreeDichotomy {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (h : ExtendedDichotomy D C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : DegreeDichotomy D C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hHI hC
  exact h X hD hHI.toExt hC

theorem ExtendedModelRank.toModelLatticeRank {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc : ℝ}
    (h : ExtendedModelRank D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc) : ModelLatticeRank D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc := by
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hHI hC
  exact h X W Qq O Kf ι σ jO w hS hHI.toExt hC

theorem ExtendedOrderBound.toOrderBoundDigits {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Ct Cc : ℝ}
    (h : ExtendedOrderBound D C0 CYb Cde Ck CD Cb CE1 CE2 Ct Cc) : OrderBoundDigits D C0 CYb Cde Ck CD Cb CE1 CE2 Ct Cc :=
  fun X hD hHI hC => h X hD hHI.toExt hC

theorem ExtendedAllConclusions.toAllConjugates {D : Formalism.BasicNotions.D7} {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs : ℝ}
    (h : ExtendedAllConclusions D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs) :
    ExportAllConjugates D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -, -⟩ := h
  exact ⟨h1.toGrowthBound, h2.toKappaBound, h3, h4, h5.toDegreeDichotomy, h6.toModelLatticeRank, h7.toOrderBoundDigits⟩

theorem Closed.mono {P P' : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop}
    (hP : ∀ C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs, P C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs →
      P' C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs) (h : Closed P) : Closed P' := by
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := h Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 Cm a1 a2 a3 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 Cm a1 a2 a3
  refine ⟨T2, hT2, fun CYb Cde Ck CD Cb b1 b2 b3 b4 b5 => ?_⟩
  obtain ⟨Ckap, Ct, Cs, c1, c2, c3, hx⟩ := h2 CYb Cde Ck CD Cb b1 b2 b3 b4 b5
  exact ⟨Ckap, Ct, Cs, c1, c2, c3, hP _ _ _ _ _ _ _ _ _ _ _ _ _ hx⟩

def HerrExtensionTheorem (D : Formalism.BasicNotions.D7) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  admitted D → ExtendedAllConclusions D C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs

def ExtendedClosedForm (D : Formalism.BasicNotions.D7) : Prop := admitted D → Closed (ExtendedAllConclusions D)

theorem ExtendedClosedForm.closed_of_extended_closed {D : Formalism.BasicNotions.D7} (h : ExtendedClosedForm D) : ClosedFormOfAdmitted D :=
  fun hA => Closed.mono (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hx => ExtendedAllConclusions.toAllConjugates hx) (h hA)

def FamilyExtendedConclusions {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), ExtendedAllConclusions (Fm.D x i) C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs

def FamilyExtendedClosed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → Closed (FamilyExtendedConclusions Fm)

def ExtendedDesignClosed (Fm : Formalism.MainNotions.DFamP) : Prop :=
  (∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), AdmF (Fm ε h0 h1)) →
    Closed fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs =>
      ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), FamilyExtendedConclusions (Fm ε h0 h1) C0 CYb Cde Ck CD Cb CE1 CE2 Cm Ckap Ct Cc Cs

end Formalism.MainNotions.ColumnSystems

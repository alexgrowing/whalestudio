import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.ObjSeg
import Formalism.SharpRestriction.GrowthBounds.ObjBridge
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.ConclusionA2
import Formalism.SharpRestriction.GrowthBounds.ColumnSystems
import Formalism.SharpRestriction.GrowthBounds.FlipOneThree

noncomputable section

namespace Formalism.MainNotions.flipOneThree

open Formalism.MainNotions.G

def EvenGapHyp {n' : ℕ} (TT : Finset (Fin n')) (G' N₁ : ℕ) : Prop :=
  ∀ j : Fin (numSeg TT), segG TT j ≤ G' ∧ segS TT j ≤ N₁

def dPrev {n' : ℕ} (TT : Finset (Fin n')) (y : Fin n') : ℕ :=
  sInf {d : ℕ | 1 ≤ d ∧ ∃ x ∈ TT, IsTypeV x ∧ posAdd x d = y}

def yPrev {n' : ℕ} (TT : Finset (Fin n')) (y : Fin n') : Fin n' :=
  ⟨(y.val + (n' - dPrev TT y % n')) % n', Nat.mod_lt _ y.pos⟩

def IaZ (m : ℕ) (Y a : ℝ) : Finset ℤ := Finset.Icc ⌈a⌉ ⌊a + a / (((m : ℝ) + 1) * Y)⌋

def IbZ (bl bu : ℝ) : Finset ℤ := Finset.Icc ⌈bl⌉ ⌊bu⌋

def meanKap {n' : ℕ} (TT : Finset (Fin n')) (m : ℕ) (Y a bl bu : ℝ) (κ : (TT → ℤ) → (TT → ℤ) → ℝ) : ℝ :=
  (∑ aa ∈ Fintype.piFinset (fun _ : TT => IaZ m Y a), ∑ bb ∈ Fintype.piFinset (fun _ : TT => IbZ bl bu),
      κ aa bb) /
    (((IaZ m Y a).card : ℝ) ^ TT.card * ((IbZ bl bu).card : ℝ) ^ TT.card)

def LaI (C₀ : ℝ) (N₁ : ℕ) (a : ℝ) : ℝ := C₀ * (N₁ : ℝ) ^ 2 * Real.log a

def deI (C C₀ : ℝ) (m N₁ : ℕ) (a b' bl bu : ℝ) : ℝ :=
  C * N₁ * LaI C₀ N₁ a / ((m : ℝ) + 1) + 2 * (bu - bl) / b'

def HypI (C₀ CH : ℝ) (p n' m : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb a b' bl bu : ℝ)
    (ccl Dp cStar : ℕ) : Prop :=
  1 ≤ Y ∧ ((m : ℝ) + 1) ^ 2 * Y ^ 2 ≤ p ∧
  (∃ x ∈ TT, IsTypeV x) ∧ 2 ≤ numSeg TT ∧ EvenGapHyp TT G' N₁ ∧ 1 ≤ N₁ ∧
  2 * N₁ + 2 ≤ m ∧
  8 * Real.log ((TT.card : ℝ) * Y) ≤ LaI C₀ N₁ a ∧
  0 < b' ∧ bl ≤ b' ∧ b' ≤ bu ∧
  Yb * TT.card * LaI C₀ N₁ a * b' / ((m : ℝ) + 1) ≤ bu - bl ∧ bu - bl ≤ b' / 2 ∧
  CH ≤ Yb ∧ 2 * Yb * TT.card * LaI C₀ N₁ a < (m : ℝ) + 1 ∧
  ((m : ℝ) + 1) * Y ^ 2 * Yb * TT.card * LaI C₀ N₁ a * Real.log a ≤ a / b' ∧
  deI CH C₀ m N₁ a b' bl bu < 1 / 6 ∧ (p : ℝ) < a / b' ∧
  CH * TT.card * LaI C₀ N₁ a ^ 2 ≤ (m : ℝ) + 1 ∧
  (∀ d : ℕ, Odd d → ¬ ((a / b') * (1 - 2 * deI CH C₀ m N₁ a b' bl bu) ≤ (p : ℝ) ^ d ∧
      (p : ℝ) ^ d ≤ (a / b') * (1 + 2 * deI CH C₀ m N₁ a b' bl bu))) ∧
  (ccl : ℝ) ≤ LaI C₀ N₁ a * b' / ((m : ℝ) + 1) ∧
  CH * TT.card * Y ^ 2 * ((N₁ : ℝ) ^ 5 + ((m : ℝ) + 1) ^ 3) * Real.logb p a ≤ Dp ∧
  8 * (Dp + 1) ≤ cStar ∧
  CH * ((m : ℝ) + 1) ^ 3 * TT.card * ((p : ℝ) ^ G') ^ 4 * ((cStar : ℝ) + TT.card * ccl + n' * ccl) * Y ≤ b'

def WeightI {n' m : ℕ} (TT : Finset (Fin n')) (Y a bl bu : ℝ) (ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) : Prop :=
  IsBaseWeight TT aw bw ccl lam0 ∧ IsDominant lam0 ∧
    ∀ s ∈ TT, aw s ∈ IaZ m Y a ∧ bw s ∈ IbZ bl bu

open Classical in

def tI (C₀ C : ℝ) (p n' m : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (a b' : ℝ) (ccl cStar : ℕ)
    (aw bw : Fin n' → ℤ) : ℝ :=
  let k : ℝ := (m : ℝ) + 1
  let N : ℝ := TT.card
  let La := LaI C₀ N₁ a
  let Q : ℝ := (p : ℝ) ^ G'
  let c : ℝ := cStar + C * N * k * Real.logb p a + 4 * N * ccl + 2 * n' * ccl
  (∑ y ∈ TT.filter (fun y => ¬ IsTypeV y),
      min (bw y : ℝ) ((aw (yPrev TT y) : ℝ) / (p : ℝ) ^ dPrev TT y)) +
    C * N * N₁ * (a / (p : ℝ) ^ 2 + b' / p + La * a / (p * k) + La * b' / k) +
    C * N * (Q * c + k * Q + k * Real.logb p a + ccl) + 2 * n' * ccl

def Conclusion2 (_D : Formalism.BasicNotions.D7) (C₀ CH C : ℝ) : Prop :=
  ∀ (p n' m : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb a b' bl bu : ℝ) (ccl Dp cStar : ℕ),
    HypI C₀ CH p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar →
    ∃ κ : (TT → ℤ) → (TT → ℤ) → ℝ,
      (∀ aa bb, 0 ≤ κ aa bb) ∧
      meanKap TT m Y a bl bu κ ≤ C * TT.card * N₁ / Y ∧
      ∀ (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
        UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
        ∀ (aw bw : Fin n' → ℤ) (lam0 : Fin n' → Fin (m + 1) → ℤ),
          WeightI TT Y a bl bu ccl aw bw lam0 →
          ∀ t : ℕ, tI C₀ C p n' m TT G' N₁ a b' ccl cStar aw bw ≤ t →
            LPprime (W := W) p n' ι σ w 1 lam0 t Dp (κ (fun s => aw s) (fun s => bw s)) cStar

def kap0I {n' : ℕ} (p m : ℕ) (TT : Finset (Fin n')) (a : ℕ) : ℝ :=
  kap0G4 (TT.card : ℝ) ((m : ℝ) + 1) p a

def lowerErrorTerm' (C₀ CE1 CE2 : ℝ) (p m G' N₁ : ℕ) (a : ℕ) (b' : ℝ) (c : ℕ) : ℝ :=
  errorTermBound CE1 CE2 p ((m : ℝ) + 1) N₁ ((p : ℝ) ^ G') c a b' (LaI C₀ N₁ a)

def m0I (Cm : ℝ) (p m G' N₁ c : ℕ) : ℝ := m0G4 Cm ((m : ℝ) + 1) N₁ ((p : ℝ) ^ G') c

def segI (C₀ CE1 CE2 : ℝ) (p n' m : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y : ℝ) (a : ℕ) (b' : ℝ) (c : ℕ)
    (bT : Fin n' → ℕ) (j : Fin (numSeg TT)) : SegData (segS TT j) :=
  segData p TT bT a b' Y (LaI C₀ N₁ a) (lowerErrorTerm' C₀ CE1 CE2 p m G' N₁ a b' c) j

def DjI (CA : ℝ) {n' : ℕ} (p m : ℕ) (TT : Finset (Fin n')) (N₁ : ℕ) (Y : ℝ) (a : ℕ) : ℝ :=
  depthD CA p a TT.card N₁ m Y

def kapTI (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (C₀ CA CE1 CE2 Cm : ℝ)
    (p n' m : ℕ) [NeZero m] (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y : ℝ) (a : ℕ) (b' : ℝ) (c : ℕ)
    (aT bT : Fin n' → ℕ) (j : Fin (numSeg TT)) : ℝ :=
  Formalism.MainNotions.G.kapT O p m (segI C₀ CE1 CE2 p n' m TT G' N₁ Y a b' c bT j) (m0I Cm p m G' N₁ c)
    (DjI CA p m TT N₁ Y a) (segATop TT aT j) (segAPlus TT aT j)

def totalDegreeBudget (CA : ℝ) {n' : ℕ} (p m : ℕ) (TT : Finset (Fin n')) (N₁ : ℕ) (Y : ℝ) (a : ℕ) : ℝ :=
  (numSeg TT : ℝ) * DjI CA p m TT N₁ Y a + 4 * kap0I p m TT a

def kapPI (C₀ CE1 CE2 Cm Ckap : ℝ) {n' : ℕ} (p m : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y : ℝ) (a : ℕ)
    (b' : ℝ) (c : ℕ) : ℝ :=
  kappaMarginBound Ckap TT.card ((m : ℝ) + 1) ((p : ℝ) ^ G') (m0I Cm p m G' N₁ c) N₁ b' Y
    (lowerErrorTerm' C₀ CE1 CE2 p m G' N₁ a b' c) a (LaI C₀ N₁ a)

def t0I (C₀ Ct : ℝ) {n' : ℕ} (p m : ℕ) (TT : Finset (Fin n')) (G' N₁ : ℕ) (a : ℕ) (b' : ℝ) (c : ℕ)
    (aT bT : Fin n' → ℕ) : ℝ :=
  t0G4 Ct p (m + 1) TT aT bT a b' (LaI C₀ N₁ a) ((p : ℝ) ^ G') c

def cleaningBudget (C₀ : ℝ) (m N₁ : ℕ) (a b' : ℝ) : ℝ := LaI C₀ N₁ a * b' / ((m : ℝ) + 1)

def WinX {n' : ℕ} (TT : Finset (Fin n')) (m : ℕ) (Y a bl bu xa xb : ℝ) (aT bT : Fin n' → ℕ) : Prop :=
  (∀ s ∈ TT, a ≤ aT s ∧ (aT s : ℝ) ≤ a + a / (((m : ℝ) + 1) * Y) + xa) ∧
  (∀ s ∈ TT, bl ≤ bT s ∧ (bT s : ℝ) ≤ bu + xb)

def CBoundI (Cc : ℝ) {n' : ℕ} (p m : ℕ) (TT : Finset (Fin n')) (a : ℕ) (ccl cStar c : ℕ) : Prop :=
  (c : ℝ) ≤ Cc * (cStar + TT.card * ((m : ℝ) + 1) * Real.logb p a + TT.card * ccl + n' * ccl)

def PathPairCorrespondence (D : Formalism.BasicNotions.D7) (C₀ CH CA CE1 CE2 Cc : ℝ) : Prop :=
  ∀ X : Inst, Conclusion1 D C₀ CH CH CH CH CH CE1 CE2 Cc CA X

def admB2 (_D : Formalism.BasicNotions.D7) (C₀ CH CA CE1 CE2 Cm Ckap Ct Cc : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m : ℕ) [NeZero m] (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb : ℝ) (a : ℕ) (b' bl bu : ℝ)
    (ccl Dp cStar : ℕ) (aT bT : Fin n' → ℕ) (c : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    HypI C₀ CH p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar →
    WinX TT m Y a bl bu (2 * cleaningBudget C₀ m N₁ a b') (2 * cleaningBudget C₀ m N₁ a b') aT bT →
    CBoundI Cc p m TT a ccl cStar c →
    4 * totalDegreeBudget CA p m TT N₁ Y a < c →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' 1 e →
      RhoGE p (beHH (m := m) p TT aT bT)
        (CCe p ι σ w TT aT bT ⌊t0I C₀ Ct p m TT G' N₁ a b' c aT bT⌋₊ c e)
        (CCe' p ι σ w TT aT bT ⌊t0I C₀ Ct p m TT G' N₁ a b' c aT bT⌋₊ c e)
        (totalDegreeBudget CA p m TT N₁ Y a)
        ((1 - kapPI C₀ CE1 CE2 Cm Ckap p m TT G' N₁ Y a b' c -
            ∑ jj, kapTI O C₀ CA CE1 CE2 Cm p n' m TT G' N₁ Y a b' c aT bT jj) *
          (dimHH (m := m) Kf TT aT bT : ℝ) / gaussianNumber (p ^ n') (m + 1))

def admB3 (_D : Formalism.BasicNotions.D7) (C₀ CH CE1 CE2 Ckap Cc Cs : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m : ℕ) [NeZero m] (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb : ℝ) (a : ℕ) (b' bl bu : ℝ)
    (ccl Dp cStar : ℕ) (aT bT : Fin n' → ℕ) (c : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    HypI C₀ CH p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar →
    WinX TT m Y a bl bu (2 * cleaningBudget C₀ m N₁ a b') (2 * cleaningBudget C₀ m N₁ a b') aT bT →
    CBoundI Cc p m TT a ccl cStar c →
    ∀ mm : ℝ, 0 ≤ mm → mm ≤ b' / (((m : ℝ) + 1) * (p : ℝ) ^ G' * Y) →
      let kp := kappaMarginBound Ckap TT.card ((m : ℝ) + 1) ((p : ℝ) ^ G') mm N₁ b' Y
        (lowerErrorTerm' C₀ CE1 CE2 p m G' N₁ a b' c) a (LaI C₀ N₁ a)
      (1 - kp) * (dimHH (m := m) Kf TT aT bT : ℝ) ≤
          gaussianNumber (p ^ n') (m + 1) *
            ∏ jj, (segRank O p m (segI C₀ CE1 CE2 p n' m TT G' N₁ Y a b' c bT jj) (segATop TT aT jj)
              (segAPlus TT aT jj) mm : ℝ) ∧
        kp ≤ Cs * TT.card * N₁ / Y

def ColumnFamilyLowerSet (_D : Formalism.BasicNotions.D7) (C₀ CH CE1 CE2 Ct Cc : ℝ) : Prop :=
  ∀ (p n' m : ℕ) [NeZero m] (TT : Finset (Fin n')) (G' N₁ : ℕ) (Y Yb : ℝ) (a : ℕ) (b' bl bu : ℝ)
    (ccl Dp cStar : ℕ) (aT bT : Fin n' → ℕ) (c : ℕ),
    p.Prime → 5 ≤ p → 2 ≤ n' → Even n' →
    HypI C₀ CH p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar →
    WinX TT m Y a bl bu (2 * cleaningBudget C₀ m N₁ a b') (2 * cleaningBudget C₀ m N₁ a b') aT bT →
    CBoundI Cc p m TT a ccl cStar c →
    ∀ bs : ∀ jj : Fin (numSeg TT), SegBlock (segS TT jj) m,
      (∀ jj, Kept p m (segI C₀ CE1 CE2 p n' m TT G' N₁ Y a b' c bT jj) (segATop TT aT jj) (bs jj)) →
      ((∑ jj, blockOrd p (segI C₀ CE1 CE2 p n' m TT G' N₁ Y a b' c bT jj) (bs jj) : ℕ) : ℝ) ≤
        t0I C₀ Ct p m TT G' N₁ a b' c aT bT

def GenericProjectionCriterion (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.NablaDeltaComparisonField D

def ColumnFamilyClosure (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.IsotypicProjectorTheoremField D ∧ Formalism.MainNotions.CovariantDegrees.FilteredProjectorCorollaryField D

def TensorColumnFamily (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.adm5 D

def BranchingColumnFamily (D : Formalism.BasicNotions.D7) : Prop := ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D

def GlobalSectionsSchur (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.AutomorphicSideConclusion D ∧ Formalism.MainNotions.CovariantDegrees.HyperplaneRank D ∧ Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D

def BracketPolynomialSpan (D : Formalism.BasicNotions.D7) : Prop :=
  Formalism.MainNotions.CovariantDegrees.GlobalSectionsSchur D ∧ Formalism.MainNotions.CovariantDegrees.BracketPolynomialSpan D ∧ Formalism.MainNotions.CovariantDegrees.GradedLatticeStable D ∧ Formalism.MainNotions.CovariantDegrees.WeylDualityLattice D

def CartanDomain : Prop :=
  ∀ (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf] (w : O), Irreducible w →
    ∀ (m : ℕ) (lam mu : Fin (m + 1) → ℤ) (Λ : Submodule O (Fin (m + 1) → Kf)), IsLattice O Λ →
    Antitone lam → Antitone mu →
    ∀ F ∈ H0 O m lam Λ, ∀ G ∈ H0 O m mu Λ, (∃ X ∈ H0 O m (lam + mu) Λ, F * G = w • X) →
      (∃ F' ∈ H0 O m lam Λ, F = w • F') ∨ ∃ G' ∈ H0 O m mu Λ, G = w • G'

def CartanOnto : Prop :=
  ∀ (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf]
    (m : ℕ) (lam mu : Fin (m + 1) → ℤ) (Λ : Submodule O (Fin (m + 1) → Kf)), IsLattice O Λ →
    Antitone lam → Antitone mu →
    H0 O m (lam + mu) Λ = Submodule.span O {X | ∃ F ∈ H0 O m lam Λ, ∃ G ∈ H0 O m mu Λ, X = F * G}

def GradedLatticeStable (_D : Formalism.BasicNotions.D7) : Prop := CartanDomain ∧ CartanOnto

def NestedTypeBound (_D : Formalism.BasicNotions.D7) : Prop := WittIdent ∧ FlatTop ∧ Formalism.MainNotions.ColumnSystems.FlatHH

def TypeDecompositionsCommute (_D : Formalism.BasicNotions.D7) : Prop := DualHeightBasis ∧ DualHeightInclusion ∧ BePerfect ∧ HLSpans

def JointComponentsPaths (_D : Formalism.BasicNotions.D7) : Prop := TestSide

def SaturatedLowerSetSpan (_D : Formalism.BasicNotions.D7) : Prop := LPOneEvery

def WeylV : Prop :=
  ∀ (Kf : Type) [Field Kf] (n' m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ((dimV Kf lam0 : ℕ) : ℚ) = ∏ s : Fin n', ∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i < j then (((lamAt lam0 s i : ℤ) : ℚ) - ((lamAt lam0 s j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1

def PairedPathIndependence (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.ColumnSystems.adm3 D ∧ WeylV

def AdmT (D : Formalism.BasicNotions.D7) : Prop :=
  GenericProjectionCriterion D ∧ ColumnFamilyClosure D ∧ TensorColumnFamily D ∧ BranchingColumnFamily D ∧ GlobalSectionsSchur D ∧ BracketPolynomialSpan D ∧ GradedLatticeStable D ∧ NestedTypeBound D ∧ TypeDecompositionsCommute D ∧ JointComponentsPaths D ∧
    SaturatedLowerSetSpan D ∧ PairedPathIndependence D

def AdmB (D : Formalism.BasicNotions.D7) (C₀ CH CA CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  PathPairCorrespondence D C₀ CH CA CE1 CE2 Cc ∧ admB2 D C₀ CH CA CE1 CE2 Cm Ckap Ct Cc ∧ admB3 D C₀ CH CE1 CE2 Ckap Cc Cs ∧
    ColumnFamilyLowerSet D C₀ CH CE1 CE2 Ct Cc ∧ AdmT D

def HodgeTateFromSandwich (D : Formalism.BasicNotions.D7) (C₀ CH CA CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  4 ≤ Cc → AdmB D C₀ CH CA CE1 CE2 Cm Ckap Ct Cc Cs →
    ∃ T C : ℝ, 0 < T ∧ 0 < C ∧ ∀ CH' : ℝ, T ≤ CH' → Conclusion2 D C₀ CH' C

def ClosedA (P : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Cc : ℝ, 0 ≤ Cc → ∃ T0 : ℝ, 0 < T0 ∧ ∀ C₀ : ℝ, T0 ≤ C₀ →
    ∃ T1 : ℝ, 0 < T1 ∧ ∀ CE1 CE2 Cm : ℝ, T1 ≤ CE1 → T1 ≤ CE2 → T1 ≤ Cm →
      ∃ T2 : ℝ, 0 < T2 ∧ ∀ CH : ℝ, T2 ≤ CH →
        ∃ CA Ckap Ct Cs : ℝ, 0 < CA ∧ 0 < Ckap ∧ 0 < Ct ∧ 0 < Cs ∧ P C₀ CH CA CE1 CE2 Cm Ckap Ct Cc Cs

def ClosedP (P : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∃ T0 : ℝ, 0 < T0 ∧ ∀ C₀ : ℝ, T0 ≤ C₀ → ∃ T2 C : ℝ, 0 < T2 ∧ 0 < C ∧ ∀ CH : ℝ, T2 ≤ CH → P C₀ CH C

def AdmBE (D : Formalism.BasicNotions.D7) : Prop := ClosedA (AdmB D)

def projection_lemma_base_level (D : Formalism.BasicNotions.D7) : Prop := ClosedP (Conclusion2 D)

def SecondPartClosed (D : Formalism.BasicNotions.D7) : Prop := AdmBE D → projection_lemma_base_level D

def AdmBF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C₀ CH CA CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), AdmB (Fm.D x i) C₀ CH CA CE1 CE2 Cm Ckap Ct Cc Cs

def Conclusion2Family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C₀ CH C : ℝ) : Prop :=
  ∀ x (i : Fm.Ix x), Conclusion2 (Fm.D x i) C₀ CH C

def SecondPartFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C₀ CH CA CE1 CE2 Cm Ckap Ct Cc Cs : ℝ) : Prop :=
  4 ≤ Cc → AdmBF Fm C₀ CH CA CE1 CE2 Cm Ckap Ct Cc Cs →
    ∃ T C : ℝ, 0 < T ∧ 0 < C ∧ ∀ CH' : ℝ, T ≤ CH' → Conclusion2Family Fm C₀ CH' C

def SecondPartFamilyClosed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ClosedA (AdmBF Fm) → ClosedP (Conclusion2Family Fm)

def UniformEpsilonConclusionClosedOfHypothesesClosed (Fm : Formalism.MainNotions.DFamP) : Prop :=
  ClosedA (fun C₀ CH CA CE1 CE2 Cm Ckap Ct Cc Cs =>
      ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), AdmBF (Fm ε h0 h1) C₀ CH CA CE1 CE2 Cm Ckap Ct Cc Cs) →
    ClosedP fun C₀ CH C => ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), Conclusion2Family (Fm ε h0 h1) C₀ CH C

end Formalism.MainNotions.flipOneThree

end

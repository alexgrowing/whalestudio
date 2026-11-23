import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.SharpRestriction.GrowthBounds.ObjBridge
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees
import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
import Formalism.SharpRestriction.GrowthBounds.ConclusionA2
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename

noncomputable section

namespace Formalism.MainNotions.tableLineDegreeFive

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

def OrbitHyp (n' : ℕ) (TT : Finset (Fin n')) (r L₁ L₂ : ℕ) (de h x : ℝ) : Prop :=
  IsGoodOrbit n' TT L₂ (r - 1) r de h x ∧ 2 * L₁ ≤ L₂ ∧ L₂ < goodU de ∧ 3 * goodG' r de h x ≤ n'

def WeightHyp {n' m : ℕ} (TT : Finset (Fin n')) (aT bT : Fin n' → ℤ) (cpp c0 : ℕ) (a : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) : Prop :=
  IsBaseWeight TT aT bT cpp lam0 ∧ IsDominant lam0 ∧
    ∀ s ∈ TT, a + cpp ≤ (aT s : ℝ) ∧ (aT s : ℝ) ≤ 2 * a - cpp ∧ 0 ≤ bT s ∧ bT s + 2 * (cpp : ℤ) ≤ c0

def La (C : ℝ) (N₁ : ℕ) (a : ℝ) : ℝ := C * (N₁ : ℝ) ^ 2 * Real.log a

def tBound (C : ℝ) (p r N N₁ L₁ G' n' k cpp c0 : ℕ) (a : ℝ) : ℝ :=
  C * r * N * (La C N₁ a * a / (p * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + c0 + k * (p : ℝ) ^ G') + 2 * r * n' * cpp

def aux₃ (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    13 ≤ p → 2 ≤ r →
    OrbitHyp n' TT r L₁ L₂ de h x →
    orbitWindowCount r de h x ^ 2 ≤ r * TT.card →
    WeightHyp TT aT bT cpp c0 a lam0 →
    (r : ℝ) ≤ Y →
    La C (orbitWindowCount r de h x) a ≤ ((m + 1 : ℕ) : ℝ) →
    orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r →
    256 * ((m + 1 : ℕ) : ℝ) ^ 2 * (TT.card : ℝ) * Y ^ 2 ≤ (p : ℝ) ^ ((L₁ : ℤ) - 1) →
    C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤ Dp →
    8 * (Dp + 1) ≤ cStar →
    C * ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * (TT.card : ℝ) * ((p : ℝ) ^ goodG' r de h x) ^ 5 *
        ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) * Y ≤ a →
    ∀ t : ℕ, tBound C p r TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) n' (m + 1) cpp c0 a ≤ t →
      LPprime (W := W) (Qq := Qq) (O := O) (Kf := Kf) p n' ι σ w r lam0 t Dp
        (C * TT.card * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y) cStar

def fwd (n' a b : ℕ) : ℕ := (b + n' - a) % n'

def topSet {n' : ℕ} (TT : Finset (Fin n')) : Finset ℕ := TT.map Fin.valEmbedding

def tile (r : ℕ) (de : ℝ) (s : ℕ) : Finset ℕ := Finset.Ico (s * goodEll r de) ((s + 1) * goodEll r de)

def NextMarked (n' r : ℕ) (de : ℝ) (T : Finset ℕ) (s s' : ℕ) : Prop :=
  s < n' / goodEll r de ∧ s' < n' / goodEll r de ∧ Formalism.G0.Marked T r (goodU de) s ∧
    Formalism.G0.Marked T r (goodU de) s' ∧
    ∀ j, 0 < j → j < (if s < s' then s' - s else s' + n' / goodEll r de - s) →
      ¬ Formalism.G0.Marked T r (goodU de) ((s + j) % (n' / goodEll r de))

def Enum (r : ℕ) (de : ℝ) (T : Finset ℕ) (s : ℕ) (f : Fin (3 * r) → ℕ) : Prop :=
  StrictMono f ∧ T ∩ tile r de s = Finset.univ.image f

def adm1 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n' : ℕ) (TT : Finset (Fin n')) (r L₁ L₂ : ℕ) (de h x : ℝ) (hr : 1 ≤ r), OrbitHyp n' TT r L₁ L₂ de h x →
    let T := topSet TT
    let u := goodU de
    let G' := goodG' r de h x
    let N₁ := orbitWindowCount r de h x
    (∀ s < n' / goodEll r de, Formalism.G0.Marked T r u s →
      ∃ f : Fin (3 * r) → ℕ, Enum r de T s f ∧ (∀ i, Even (f i)) ∧
        ∀ i, ∀ y ∈ T, y ≠ f i → u < fwd n' y (f i) ∧ u < fwd n' (f i) y) ∧
    (∀ s s' (f f' : Fin (3 * r) → ℕ), NextMarked n' r de T s s' → Enum r de T s f → Enum r de T s' f' →
      let a := f ⟨r, by omega⟩
      let b := f' ⟨2 * r - 1, by omega⟩
      let Dd := fwd n' a b
      Dd + 1 ≤ G' ∧ (T ∩ (Finset.range (Dd + 1)).image (fun j => (a + j) % n')).card ≤ N₁ ∧
        (∀ i : Fin (3 * r), 2 * r ≤ i.val → Even (f i)) ∧ (∀ i : Fin (3 * r), i.val < r → Even (f' i)) ∧
        (∀ (i : Fin (3 * r)) (hi : i.val + 1 < 3 * r), 2 * r ≤ i.val + 1 → f i + L₂ < f ⟨i.val + 1, hi⟩) ∧
        (∀ (i : Fin (3 * r)) (hi : i.val + 1 < 3 * r), i.val < r → f' i + L₂ < f' ⟨i.val + 1, hi⟩)) ∧
    (∀ i ∈ T, (T.filter fun y => Even y ∧ 1 ≤ fwd n' y i ∧ fwd n' y i ≤ L₁).card < r) ∧
    (∀ y ∈ T, Even y → ∃ d, 1 ≤ d ∧ d ≤ G' ∧ (y + d) % n' ∈ T ∧ Even ((y + d) % n') ∧
      (∀ d', 1 ≤ d' → d' < d → (y + d') % n' ∈ T → ¬ Even ((y + d') % n')) ∧
      (T ∩ (Finset.Ioo 0 d).image (fun j => (y + j) % n')).card ≤ N₁)

def adm2 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    let h := 2 + 8 * eps
    let r := ⌈8 * (h + 2) / eps⌉₊ + 1
    let de := x ^ (-(eps / 8))
    (goodG' r de h x : ℝ) ≤ C * Real.log x / de ∧ (orbitWindowCount r de h x : ℝ) ≤ C * Real.log x ∧
    ∀ n' : ℕ, x ^ (eps / 4) ≤ n' → 3 * goodG' r de h x ≤ n' ∧
      ∀ (TT : Finset (Fin n')) (L₂ : ℕ), IsGoodOrbit n' TT L₂ (r - 1) r de h x →
        (n' : ℝ) * de / (C * Real.log x) ≤ TT.card ∧ (TT.card : ℝ) ≤ 40 * n' * de

def adm3 (_D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.G.DualHeightInclusion

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.G.BePerfect

def adm5 (_D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.G.LPOneEvery

def HerrCocycleExtensionClass (_D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.G.WittIdent

def FontaineFormalProperties (_D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.G.FlatTop

def AmbientMetricLowerBound (_D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.G.DualHeightBasis

def HostOrbitConditions (_D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.G.HLSpans

def OrderConsequences (_D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.G.TestSide

def FewBadOrbits (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (Kf : Type) [Field Kf] (n' m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ((dimV Kf lam0 : ℕ) : ℚ) = ∏ s : Fin n', ∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i < j then (((lamAt lam0 s i : ℤ) : ℚ) - ((lamAt lam0 s j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1

def LevelPrimesProviso (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (O Kf : Type) [CommRing O] [Field Kf] [Algebra O Kf] (n' m : ℕ) (lam0 mu0 : Fin n' → Fin (m + 1) → ℤ)
    (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)), IsDominant lam0 → IsDominant mu0 →
    ∀ F ∈ Hten O lam0 Λ, ∀ G ∈ Hten O mu0 Λ, F * G ∈ Hten O (lam0 + mu0) Λ

def VGe (p : ℕ) (x : ℚ) (c : ℝ) : Prop := x = 0 ∨ c ≤ (padicValRat p x : ℝ)

def mahlerCoef (f : ℕ → ℚ) (j : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (j + 1), (-1 : ℚ) ^ (j - i) * (j.choose i : ℚ) * f i

def harm (P s : ℕ) : ℚ := ∑ y ∈ Finset.Ico 1 P, ((y : ℚ) ^ s)⁻¹

def powSum (s n : ℕ) : ℚ := ∑ i ∈ Finset.range n, (i : ℚ) ^ s

def plog (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) : ℚ_[p] :=
  ∑' k : ℕ, (-1 : ℚ_[p]) ^ k * (x - 1) ^ (k + 1) / ((k : ℚ_[p]) + 1)

def BinomDecay (p : ℕ) (f : ℕ → ℚ) : Prop := ∀ j : ℕ, VGe p (mahlerCoef f j) ((j : ℝ) / 4)

def adm22 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ t : ℕ,
    let P := p ^ (t + 1)
    (∀ n : ℕ, cUnit P n = ∏ i ∈ Finset.range n, ∏ y ∈ Finset.Ico 1 P, (1 + (P : ℚ) * i / y)) ∧
    (∀ n : ℕ, plog p (cUnit P n : ℚ_[p]) =
      ∑' s : ℕ, (((-1 : ℚ) ^ s * (P : ℚ) ^ (s + 1) * harm P (s + 1) / ((s : ℚ) + 1) * powSum (s + 1) n : ℚ) : ℚ_[p])) ∧
    (∀ s : ℕ, 1 ≤ s → (s : ℤ) ≤ padicValRat p ((P : ℚ) ^ s * harm P s)) ∧
    (∀ s : ℕ, ∃ f : Polynomial ℚ, f.natDegree = s + 1 ∧ ∀ n : ℕ, f.eval (n : ℚ) = powSum s n) ∧
    (∀ s : ℕ, 1 ≤ s → ((s : ℝ) + 1) / 4 ≤
      (padicValRat p ((-1 : ℚ) ^ (s - 1) * (P : ℚ) ^ s * harm P s / s) : ℝ) - 1 / ((p : ℝ) - 1)) ∧
    BinomDecay p (fun n => cUnit P n) ∧ BinomDecay p (fun n => (cUnit P n)⁻¹) ∧
    (∀ rho : ℕ, rho < P → BinomDecay p (fun n => dUnit P n rho) ∧ BinomDecay p (fun n => (dUnit P n rho)⁻¹)) ∧
    (∀ (K : ℕ) (f : Fin K → ℕ → ℚ), (∀ k, BinomDecay p (f k)) → ∀ c : ℕ,
      ∃ b : (Fin K → ℕ) → ℚ,
        (∀ J, b J ≠ 0 → ∑ k, J k ≤ 4 * c ∧ 0 ≤ padicValRat p (b J)) ∧
        ∀ n : Fin K → ℕ, VGe p (∏ k, f k (n k) -
          ∑ J ∈ Fintype.piFinset (fun _ : Fin K => Finset.range (4 * c + 1)),
            b J * ∏ k, ((n k).choose (J k) : ℚ)) c)

def jointComp {O : Type} [CommRing O] [IsDomain O] {ι : Type} [Fintype ι] (n : ℕ) (LL : Letters ι) {N : ℕ}
    (Ss : Fin N → Set ι) (t : Fin N → Fin n → ℤ) : Submodule (KK O) (MvPolynomial (ι × Fin n) (KK O)) :=
  ⨅ i, isoSub (glOps (KK O) n LL (Ss i)) (t i)

def adm11 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.FilteredProjectorCorollaryField D

def FilteredProjectionCriterion (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (ι : Type) [Fintype ι] (LL : Letters ι) (N : ℕ) (Ss : Fin N → Set ι), Monotone Ss →
      (∀ (S : Set ι) (a b : Fin n) (k : ℕ), a ≠ b →
        ((k.factorial : ℕ) : KK O) • divPow (KK O) LL S a b k = (glAct (KK O) LL S a b) ^ k) ∧
      (∀ (S : Set ι) (a b : Fin n) (F G : MvPolynomial (ι × Fin n) (KK O)),
        fock (glAct (KK O) LL S a b F) G = fock F (glAct (KK O) LL S b a G)) ∧
      (∀ (d : ι → ℕ) (i : Fin N), ellOf (glOps (KK O) n LL (Ss i)) (Pol (KK O) n d) ≤ degIn d (Ss i)) ∧
      ∀ ee : Fin N → (Fin n → ℤ) → Module.End (KK O) (MvPolynomial (ι × Fin n) (KK O)),
        (∀ i lam, IsIsoProj (glOps (KK O) n LL (Ss i)) lam (ee i lam)) →
        (∀ i j : Fin N, i < j → ∀ lam a b, ee i lam * glAct (KK O) LL (Ss j) a b = glAct (KK O) LL (Ss j) a b * ee i lam) ∧
        (∀ (T : Finset (Fin N → Fin n → ℤ)) (e : Module.End (KK O) (MvPolynomial (ι × Fin n) (KK O))),
          (∀ t ∈ T, ∀ x ∈ jointComp (O := O) n LL Ss t, e x = x) →
          (∀ t ∉ T, ∀ x ∈ jointComp (O := O) n LL Ss t, e x = 0) →
          e = ∑ t ∈ T, (List.ofFn fun i => ee i (t i)).prod) ∧
        (∀ (d : ι → ℕ) (i : Fin N) (lam : Fin n → ℤ), (∃ F ∈ Pol (KK O) n d, ee i lam F ≠ 0) →
          ellWt lam ≤ degIn d (Ss i)) ∧
        (∀ (T : Finset (Fin N → Fin n → ℤ)) (d : ι → ℕ) (i : Fin N),
          (∀ t ∈ T, ellWt (t i) ≤ degIn d (Ss i)) →
          ((T.sup fun t =>
              N0 n * deF p n (ellOf (glOps (KK O) n LL (Ss i)) (Pol (KK O) n d) + ellWt (t i)) : ℕ) : ℝ) ≤
            (N0 n : ℝ) * Real.logb p (2 * (degIn d (Ss i) : ℝ) + n))

def adm6 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.adm5 D

def adm7 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.InvariantProjectionField D

def adm8 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.NablaDeltaComparisonField D

def adm9 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.IsotypicProjectorTheoremField D

def adm10 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.TranslateCorollaryField D

def adm12 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.ValuationLemmaField D

def adm21 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.ConclusionE D

def adm23 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.UnitProductSecondLemma D

def FrobeniusExpansionCongruence (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.DerivativeLemma D

def HerrExtensionClause (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.SelectionLemmas.admB2 D

def adm26 (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop := Formalism.MainNotions.SelectionLemmas.Conclusion2 D CLa Ck Crk Cdeg

def TopsChoiceLemma (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.SelectionLemmas.NestedTypeBound D

def ZeroGainAbove (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.SelectionLemmas.PathPairCorrespondence D

def ChosenTopsCount (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.SelectionLemmas.TypeDecompositionsCommute D

def adm13 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.AutomorphicSideConclusion D

def adm14 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.HyperplaneRank D

def adm15 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D

def adm16 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.RotatedSumBound D

def adm17 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.PathWeightComponents D

def adm18 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.ConclusionB3 D

def adm19 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.CoefficientDependence D

def adm20 (D : Formalism.BasicNotions.D7) : Prop := Formalism.MainNotions.CovariantDegrees.CanonicalTranslateJetIdentity D

def admitted (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D ∧ adm8 D ∧ adm9 D ∧ adm10 D ∧ adm11 D ∧ FilteredProjectionCriterion D ∧
    adm12 D ∧ adm13 D ∧ adm14 D ∧ adm15 D ∧ adm16 D ∧ adm17 D ∧ adm18 D ∧ adm19 D ∧ adm20 D ∧ adm21 D ∧
    adm22 D ∧ adm23 D ∧ FrobeniusExpansionCongruence D ∧ HerrExtensionClause D ∧ adm26 D CLa Ck Crk Cdeg ∧ HerrCocycleExtensionClass D ∧ FontaineFormalProperties D ∧ AmbientMetricLowerBound D ∧ HostOrbitConditions D ∧
    OrderConsequences D ∧ TopsChoiceLemma D ∧ ZeroGainAbove D ∧ ChosenTopsCount D ∧ FewBadOrbits D ∧ LevelPrimesProviso D

def Stmt (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg C : ℝ) : Prop := admitted D CLa Ck Crk Cdeg → aux₃ D C

def ConclusionE (D : Formalism.BasicNotions.D7) : Prop := ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → aux₃ D C

def ClosedFormOfAdmitted (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ CLa Ck Crk Cdeg : ℝ, admitted D CLa Ck Crk Cdeg → ConclusionE D

def OrbitValuationBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ i : Fm.Ix x, aux₃ (Fm.D x i) C

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  ∀ (x : ℝ) (i : Fm.Ix x), admitted (Fm.D x i) CLa Ck Crk Cdeg

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (CLa Ck Crk Cdeg C : ℝ) : Prop :=
  AdmF Fm CLa Ck Crk Cdeg → OrbitValuationBound Fm C

def FamilyClosedForm {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ CLa Ck Crk Cdeg : ℝ, AdmF Fm CLa Ck Crk Cdeg →
    ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ x : ℝ, x₀ ≤ x → ∀ i : Fm.Ix x, aux₃ (Fm.D x i) C

def SecondTheoremDesignData (Fm : Formalism.MainNotions.DFamP) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), OrbitValuationBound (Fm ε h0 h1) C

def AdmDF (Fm : Formalism.MainNotions.DFamP) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), AdmF (Fm ε h0 h1) CLa Ck Crk Cdeg

def DerivativeStatementDesign (Fm : Formalism.MainNotions.DFamP) : Prop :=
  ∀ CLa Ck Crk Cdeg : ℝ, AdmDF Fm CLa Ck Crk Cdeg → SecondTheoremDesignData Fm

end Formalism.MainNotions.tableLineDegreeFive

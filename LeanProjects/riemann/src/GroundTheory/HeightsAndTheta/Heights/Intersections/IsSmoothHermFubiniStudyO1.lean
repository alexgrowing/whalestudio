import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

variable (ι) in

abbrev Family := Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ

def coneSet : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}

def AllSmooth {n : ℕ} (L : Fin n → HermLine ι) : Prop := ∀ j, IsSmoothHerm (L j)

def degs {n : ℕ} (L : Fin n → HermLine ι) : Fin n → K → ℤ := fun j => (L j).a

def pots {n : ℕ} (L : Fin n → HermLine ι) : Fin n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => Real.log ((L j).h z)

def IsSec (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) : Prop :=
  ∃ a : K → ℕ, IsMultiHomog s a ∧ (∀ k, (a k : ℤ) = A.a k) ∧ s ∉ P

open Classical in

def horizPart (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) : ℝ :=
  ∑ W ∈ (divSupp_finite P s).toFinset.filter (fun W => IsHorizontal W),
    (multAt (P ⊔ Ideal.span {s}) W : ℝ) * I W n L

open Classical in

def vertPart (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) : ℝ :=
  ∑ V ∈ (divSupp_finite P s).toFinset.filter (fun V => ¬ IsHorizontal V),
    (multAt (P ⊔ Ideal.span {s}) V : ℝ) * (geoNum n V (degs L) : ℝ) * Real.log (charOf V)

def intPart (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) : ℝ :=
  ptsIntegral P (pots L) (logNorm A s)

def rhsR (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι)
    (s : MRing ι) : ℝ :=
  horizPart I P L s + vertPart P L s - intPart P L A s

def logNormQ (A : HermLine ι) (f g : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)

def rhsRQ (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι)
    (f g : MRing ι) : ℝ :=
  horizPart I P L f - horizPart I P L g + (vertPart P L f - vertPart P L g) -
    ptsIntegral P (pots L) (logNormQ A f g)

def IsFamilyOn (I : Family ι) (good : ℕ → Prop) : Prop :=
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)),
      good n → IsArithVar P n → AllSmooth L → I P n (L ∘ σ) = I P n L) ∧
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (j : Fin n) (A B : HermLine ι),
      good n → IsArithVar P n → AllSmooth L → IsSmoothHerm A → IsSmoothHerm B →
      I P n (Function.update L j (A.tensor B)) =
        I P n (Function.update L j A) + I P n (Function.update L j B)) ∧
  (∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin (n + 1) → HermLine ι) (s : MRing ι),
      good (n + 1) → IsArithVar P (n + 1) → AllSmooth L → IsSec P (L (Fin.last n)) s →
      I P (n + 1) L = rhsR I P (Fin.init L) (L (Fin.last n)) s)

def IsFamily (I : Family ι) : Prop := IsFamilyOn I fun _ => True

def expLine (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) : HermLine ι where
  a := 0
  h z := Real.exp (u z / 2)
  pos _ _ := Real.exp_pos _
  smul c z hc := by simp [hu c z hc]

def IsClosedPt (x : Ideal (MRing ι)) : Prop :=
  IsMultiProjPrime x ∧ ringKrullDim (MRing ι ⧸ x) = ((Fintype.card K : ℕ) : WithBot ℕ∞)

end Objects

def ThmIExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ∃ I : Family ι, IsFamily I

def ThmIUnique.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I J : Family ι),
    IsFamily I → IsFamily J → ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι),
      IsArithVar P n → AllSmooth L → I P n L = J P n L

def R1.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 →
    (∀ (I J : Family ι) (A : HermLine ι) (s s' : MRing ι), IsSmoothHerm A → IsSec P A s → IsSec P A s' →
        rhsR I P ![] A s = rhsR J P ![] A s') ∧
    (∀ (I : Family ι) (A B : HermLine ι) (s t : MRing ι), IsSmoothHerm A → IsSmoothHerm B →
        IsSec P A s → IsSec P B t →
        rhsR I P ![] (A.tensor B) (s * t) = rhsR I P ![] A s + rhsR I P ![] B t)

def Swap.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι) (n : ℕ),
    IsFamilyOn I (· < n + 2) →
    ∀ (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s s' : MRing ι),
      IsArithVar P (n + 2) → AllSmooth L → IsSmoothHerm A → IsSmoothHerm B →
      IsSec P A s → IsSec P B s' → Disjoint (divSupp P s) (divSupp P s') →
      rhsR I P (Fin.snoc L B) A s = rhsR I P (Fin.snoc L A) B s'

def Choice.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ),
    IsArithVar P d → ∀ (m : ℕ) (W x : Fin m → Ideal (MRing ι)),
      (∀ i, IsMultiProjPrime (W i) ∧ P ≤ W i) → (∀ i, W i ≤ x i ∧ IsClosedPt (x i)) →
      ∀ (a : K → ℤ) (b : K → ℕ), (∀ j, 1 ≤ b j) → ∃ k₀ : ℕ, ∀ k ≥ k₀,
        (∀ j, 0 ≤ a j + k * b j) ∧
        (∃ s : MRing ι, IsMultiHomog s (fun j => (a j + k * b j).toNat) ∧ ∀ i, s ∉ x i) ∧
        (∃ s : MRing ι, IsMultiHomog s (fun j => k * b j) ∧ ∀ i, s ∉ x i)

def ArithmeticIntersectionSecond.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (u : ((Σ k, ι k) → ℂ) → ℝ)
      (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z),
      IsArithVar P (n + 1) → AllSmooth L → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u coneSet →
      I P (n + 1) (Fin.snoc L (expLine u hu)) = (1 / 2) * ptsIntegral P (pots L) u

def InductiveIntersectionFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (f g : MRing ι)
      (α β : K → ℕ), IsArithVar P (n + 1) → AllSmooth L → IsSmoothHerm A →
      IsMultiHomog f α → IsMultiHomog g β → (∀ k, (α k : ℤ) - β k = A.a k) → f ∉ P → g ∉ P →
      (∀ W, IsHorizontal W → divCycle P f W = divCycle P g W) →
      (∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ =
        ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z) →
      I P (n + 1) (Fin.snoc L A) = vertPart P L f - vertPart P L g

def ArithmeticIntersectionFifth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι), IsArithVar P 1 → IsSmoothHerm A →
      IsSec P A s → I P 1 ![A] = vertPart P ![] s - intPart P ![] A s

def Conservation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (p : ℕ), IsArithVar P (n + 1) → AllSmooth L → p.Prime →
    ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (degs L) : ℝ) =
      ptsIntegral P (pots L) (fun _ => 1)

def RationalSections.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι), IsFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (f g : MRing ι)
      (α β : K → ℕ), IsArithVar P (n + 1) → AllSmooth L → IsSmoothHerm A →
      IsMultiHomog f α → IsMultiHomog g β → (∀ k, (α k : ℤ) - β k = A.a k) → f ∉ P → g ∉ P →
      I P (n + 1) (Fin.snoc L A) = rhsRQ I P L A f g

section Inhabitants

abbrev GlobalTheory (n : ℕ) : Unit → Type := fun _ => Fin n

abbrev Xb (n : ℕ) (i : Fin n) : MRing (GlobalTheory n) := X ⟨(), i⟩

def fsO1 (n : ℕ) : HermLine (GlobalTheory n) := HermLine.sqMetric fun _ => 1

def triv (n : ℕ) : HermLine (GlobalTheory n) := HermLine.sqMetric fun _ => 0

example : Family (GlobalTheory 2) := fun _ _ _ => 0

theorem isSmoothHerm_fubiniStudyO1 (n : ℕ) : IsSmoothHerm (fsO1 n) := isSmoothHerm_sqMetric _

theorem isArithVar_bot (n : ℕ) : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (n + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    simp [Nat.card_eq_fintype_card]
    exact add_comm _ _

theorem isMultiHomog_Xb (n : ℕ) (i : Fin n) : IsMultiHomog (Xb n i) fun _ => 1 := by
  intro m hm k
  rw [support_X] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  cases k
  simp [Finsupp.single_apply]

theorem isMultiHomog_C (c : ℤ) {n : ℕ} : IsMultiHomog (C c : MRing (GlobalTheory n)) 0 := by
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem isSec_Xb (n : ℕ) (i : Fin (n + 1)) : IsSec (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (fsO1 (n + 1)) (Xb (n + 1) i) :=
  ⟨fun _ => 1, isMultiHomog_Xb _ _, fun _ => by simp [fsO1, HermLine.sqMetric],
    by rw [Ideal.mem_bot]; exact X_ne_zero _⟩

theorem specInt_hypotheses_hold : IsArithVar (⊥ : Ideal (MRing (GlobalTheory 1))) 1 ∧ IsSmoothHerm (fsO1 1) ∧
    IsSec (⊥ : Ideal (MRing (GlobalTheory 1))) (fsO1 1) (Xb 1 0) :=
  ⟨isArithVar_bot 0, isSmoothHerm_fubiniStudyO1 1, isSec_Xb 0 0⟩

def halfLine : HermLine (GlobalTheory 1) := expLine (fun _ => 2 * Real.log 2) fun _ _ _ => rfl

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

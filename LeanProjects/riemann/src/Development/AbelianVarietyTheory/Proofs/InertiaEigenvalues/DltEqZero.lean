import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology Classical

variable {K : UQ} (B : InvAlg K) {ι : Type}

abbrev al (K : UQ) (a : K.O) : K.E := algebraMap K.O K.E a

def InDual (s : B.A) (M : Submodule K.O B.A) : Prop :=
  ∀ z ∈ M, Algebra.trace K.E B.A (s * z) ∈ (algebraMap K.O K.E).range

def indM (M : Submodule K.O B.A) (y : B.A) : ℚ := if y ∈ M then 1 else 0

def indD (M : Submodule K.O B.A) (s : B.A) : ℚ := if InDual B s M then 1 else 0

def dlt {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (y : A) : ℚ :=
  ∑ J ∈ I.powerset, (-1 : ℚ) ^ J.card * f ((∏ j ∈ J, π j) * y)

def term (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) : ℚ :=
  dlt π I (indM B M) u * dlt π I' (indD B M) s

def HH (π : ι → B.A) (I I' : Finset ι) (u s : B.A) : ℚ :=
  ∑ᶠ M ∈ B.Lin, B.sgnLat M * term B π I I' u s M

def eS (e : ι → B.A) (I : Finset ι) : B.A := ∑ i ∈ I, e i

def Pos (a : K.O) (e : ι → B.A) (N : ℕ) (M : Submodule K.O B.A) (p : ι → ℤ) : Prop :=
  ∀ i, (∀ r : B.A, IsIntegral K.O r → (al K a ^ (p i + N)) • (e i * r) ∈ M) ∧
    ∀ m ∈ M, IsIntegral K.O ((al K a ^ (-p i)) • (e i * m))

def chi (e : ι → B.A) (I : Finset ι) (y : B.A) : ℚ :=
  K.eta (Algebra.norm K.E (y * eS B e I + (1 - eS B e I)))

def IsPre [Fintype ι] (e : ι → B.A) (S : Finset ι) : Prop :=
  CompleteOrthogonalIdempotents e ∧ ∀ i, ∃ f : B.A, IsIdempotentElem f ∧ f ≠ 0 ∧
    (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
    (i ∈ S → e i = f ∧ B.σ f = f) ∧ (i ∉ S → f * B.σ f = 0 ∧ e i = f + B.σ f)

def IsFrame [Fintype ι] (e π : ι → B.A) (S : Finset ι) : Prop :=
  IsPre B e S ∧ ∀ i ∈ S, B.Plus (π i) ∧ π i * (1 - e i) = 1 - e i ∧ K.eta (Algebra.norm K.E (π i)) = -1

def Win (I I' : Finset ι) (L k : ℕ) (p : ι → ℤ) : Prop :=
  ∀ i, -(L : ℤ) ≤ p i ∧ p i ≤ 2 * k + L ∧ (i ∈ I → 2 * (k : ℤ) - L ≤ p i) ∧ (i ∈ I' → p i ≤ L)

def Mid (S : Finset ι) (L k : ℕ) (p : ι → ℤ) : Prop :=
  ∀ i ∉ S, (L : ℤ) ≤ p i ∧ p i ≤ 2 * k - L

theorem eta_mul {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy), neg_add, zpow_add₀ (by norm_num)]

theorem eta_sq (x : K.E) : K.eta x * K.eta x = 1 := by
  unfold UQ.eta
  rw [← mul_zpow]; simp

theorem abs_eta (x : K.E) : |K.eta x| = 1 := by
  unfold UQ.eta; simp

theorem abs_indM (M : Submodule K.O B.A) (y : B.A) : |indM B M y| ≤ 1 := by
  unfold indM; split_ifs <;> simp

theorem abs_indD (M : Submodule K.O B.A) (y : B.A) : |indD B M y| ≤ 1 := by
  unfold indD; split_ifs <;> simp

theorem abs_dlt {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (hf : ∀ y, |f y| ≤ 1) (y : A) :
    |dlt π I f y| ≤ 2 ^ I.card := by
  unfold dlt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ J ∈ I.powerset, |(-1 : ℚ) ^ J.card * f ((∏ j ∈ J, π j) * y)| ≤ ∑ J ∈ I.powerset, (1 : ℚ) :=
        Finset.sum_le_sum fun J _ => by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hf _
    _ = 2 ^ I.card := by simp [Finset.card_powerset]

theorem abs_term (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) :
    |term B π I I' u s M| ≤ 2 ^ I.card * 2 ^ I'.card := by
  unfold term
  rw [abs_mul]
  exact mul_le_mul (abs_dlt _ _ _ (abs_indM B M) _) (abs_dlt _ _ _ (abs_indD B M) _) (abs_nonneg _) (by positivity)

theorem dlt_eq_zero {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (y : A) (i : ι) (hi : i ∈ I)
    (h : ∀ J ⊆ I.erase i, f (π i * ((∏ j ∈ J, π j) * y)) = f ((∏ j ∈ J, π j) * y)) : dlt π I f y = 0 := by
  unfold dlt
  rw [← Finset.insert_erase hi, Finset.sum_powerset_insert (Finset.notMem_erase i I)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun J hJ => ?_
  have hJ' : i ∉ J := fun h => Finset.notMem_erase i I (Finset.mem_powerset.1 hJ h)
  rw [Finset.prod_insert hJ', Finset.card_insert_of_notMem hJ', mul_assoc, h J (Finset.mem_powerset.1 hJ)]
  ring

end GlobalTheory.UnitLemma.Desc

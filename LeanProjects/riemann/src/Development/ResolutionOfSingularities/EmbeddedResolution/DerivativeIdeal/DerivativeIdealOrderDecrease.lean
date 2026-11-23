import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealOrder
namespace FunctorialResolution.EmbeddedResolution

open IsLocalRing

noncomputable def eulerDerivation (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) : Derivation k R R :=
  ∑ i, x i • D i

private theorem sum_smul_derivation_apply (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} (s : Finset ι) (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    (∑ i ∈ s, x i • D i) a = ∑ i ∈ s, x i * D i a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply,
        Derivation.smul_apply, smul_eq_mul, ih]

theorem eulerDerivation_apply (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    eulerDerivation k x D a = ∑ i, x i * D i a := by
  show (∑ i, x i • D i) a = ∑ i, x i * D i a
  exact sum_smul_derivation_apply k Finset.univ x D a

theorem eulerDerivation_apply_mem_span (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    eulerDerivation k x D a ∈ Ideal.span (Set.range x) := by
  rw [eulerDerivation_apply]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem eulerDerivation_apply_generator (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (j : ι) :
    eulerDerivation k x D (x j) = x j := by
  rw [eulerDerivation_apply]
  simp [hD]

private theorem eulerDerivation_sub_self_mem_sq (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {f : R}
    (hf : f ∈ Ideal.span (Set.range x)) :
    eulerDerivation k x D f - f ∈ Ideal.span (Set.range x) ^ 2 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      rw [eulerDerivation_apply_generator k x D hD j, sub_self]
      exact Submodule.zero_mem _
  | zero =>
      rw [map_zero, sub_zero]
      exact Submodule.zero_mem _
  | add a b _ _ iha ihb =>
      have key : eulerDerivation k x D (a + b) - (a + b)
          = (eulerDerivation k x D a - a) + (eulerDerivation k x D b - b) := by
        rw [map_add]; ring
      rw [key]
      exact Submodule.add_mem _ iha ihb
  | smul c a ha iha =>
      have key : eulerDerivation k x D (c • a) - c • a
          = c * (eulerDerivation k x D a - a) + a * eulerDerivation k x D c := by
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
      rw [key]
      refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ iha) ?_
      have h2 := Ideal.mul_mem_mul ha (eulerDerivation_apply_mem_span k x D c)
      rwa [← pow_two] at h2

private theorem forall_eulerDerivation_sub_natCast_mul_mem (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (r : ℕ) :
    ∀ f : R, f ∈ Ideal.span (Set.range x) ^ r →
      eulerDerivation k x D f - (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
  induction r with
  | zero =>
      intro f _
      have h := eulerDerivation_apply_mem_span k x D f
      simpa using h
  | succ r ih =>
      intro f hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb
        have hEb := eulerDerivation_sub_self_mem_sq k x D hD hb
        have hEa := ih a ha
        have h1 : a * (eulerDerivation k x D b - b) ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          have h := Ideal.mul_mem_mul ha hEb
          rwa [← pow_add] at h
        have h2 : (eulerDerivation k x D a - (r : R) * a) * b
            ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          have hb1 : b ∈ Ideal.span (Set.range x) ^ 1 := by rwa [pow_one]
          have h := Ideal.mul_mem_mul hEa hb1
          have e : r + 1 + 1 = r + 2 := by omega
          rw [← pow_add, e] at h
          exact h
        have key : eulerDerivation k x D (a * b) - ((r + 1 : ℕ) : R) * (a * b)
            = a * (eulerDerivation k x D b - b) + (eulerDerivation k x D a - (r : R) * a) * b := by
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
          push_cast
          ring
        have hres : eulerDerivation k x D (a * b) - ((r + 1 : ℕ) : R) * (a * b)
            ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          rw [key]
          exact Submodule.add_mem _ h1 h2
        exact hres
      · intro y z hy hz
        have key : eulerDerivation k x D (y + z) - ((r + 1 : ℕ) : R) * (y + z)
            = (eulerDerivation k x D y - ((r + 1 : ℕ) : R) * y)
              + (eulerDerivation k x D z - ((r + 1 : ℕ) : R) * z) := by
          rw [map_add]; ring
        have hres : eulerDerivation k x D (y + z) - ((r + 1 : ℕ) : R) * (y + z)
            ∈ Ideal.span (Set.range x) ^ (r + 1 + 1) := by
          rw [key]
          exact Submodule.add_mem _ hy hz
        exact hres

theorem eulerDerivation_sub_natCast_mul_mem_pow_succ (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (r : ℕ) {f : R}
    (hf : f ∈ Ideal.span (Set.range x) ^ r) :
    eulerDerivation k x D f - (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) :=
  forall_eulerDerivation_sub_natCast_mul_mem k x D hD r f hf

theorem mem_pow_succ_of_deriv_mem_pow (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {r : ℕ} (hr : IsUnit ((r : ℕ) : R))
    {f : R} (hf : f ∈ Ideal.span (Set.range x) ^ r)
    (hdf : ∀ i, D i f ∈ Ideal.span (Set.range x) ^ r) :
    f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
  have hgen : ∀ i, x i * D i f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    intro i
    have hx1 : x i ∈ Ideal.span (Set.range x) ^ 1 := by
      rw [pow_one]
      exact Ideal.subset_span ⟨i, rfl⟩
    have h := Ideal.mul_mem_mul hx1 (hdf i)
    rw [← pow_add, Nat.add_comm 1 r] at h
    exact h
  have h1 : eulerDerivation k x D f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    rw [eulerDerivation_apply]
    exact Ideal.sum_mem _ fun i _ => hgen i
  have h2 := eulerDerivation_sub_natCast_mul_mem_pow_succ k x D hD r hf
  have h3 : (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    have h := Submodule.sub_mem _ h1 h2
    simpa using h
  obtain ⟨u, hu⟩ := hr
  have key : (↑u⁻¹ : R) * ((r : R) * f) = f := by
    rw [← hu, ← mul_assoc, u.inv_mul, one_mul]
  rw [← key]
  exact Ideal.mul_mem_left _ _ h3

theorem not_derivIdeal_le_pow (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {r : ℕ} (hr : IsUnit ((r : ℕ) : R))
    {I : Ideal R} (h1 : I ≤ Ideal.span (Set.range x) ^ r)
    (h2 : ¬ I ≤ Ideal.span (Set.range x) ^ (r + 1)) :
    ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r := by
  intro h
  apply h2
  intro f hf
  exact mem_pow_succ_of_deriv_mem_pow k x D hD hr (h1 hf)
    (fun i => h (derivation_apply_mem_derivIdeal k I (D i) hf))

private theorem eq_natCast_of_le_of_not_succ_le (n : ℕ) (a : ℕ∞) (h1 : (n : ℕ∞) ≤ a)
    (h2 : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ a) : a = (n : ℕ∞) := by
  rcases eq_top_or_lt_top a with rfl | hlt
  · exact absurd le_top h2
  · lift a to ℕ using hlt.ne
    have hn : n ≤ a := by exact_mod_cast h1
    have hn2 : ¬ (n + 1 ≤ a) := by
      intro hc
      exact h2 (by exact_mod_cast hc)
    have ha : a = n := by omega
    exact_mod_cast ha

theorem idealOrder_derivIdeal_of_isUnit_natCast (k : Type*) [CommRing k] {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {I : Ideal R} {r : ℕ} (hr : 1 ≤ r) (hI : idealOrder I = (r : ℕ∞)) :
    idealOrder (derivIdeal k I) = ((r - 1 : ℕ) : ℕ∞) := by
  have hIr : I ≤ IsLocalRing.maximalIdeal R ^ r := (le_idealOrder_iff I r).mp hI.ge
  have hIr1 : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (r + 1) := by
    intro hc
    have h := (le_idealOrder_iff I (r + 1)).mpr hc
    rw [hI] at h
    have h' : r + 1 ≤ r := by exact_mod_cast h
    omega
  have hunitr : IsUnit ((r : ℕ) : R) := hunit r hr
  have hnot : ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r :=
    not_derivIdeal_le_pow k x D hD hunitr (by rw [hx]; exact hIr) (by rw [hx]; exact hIr1)
  have hle : derivIdeal k I ≤ IsLocalRing.maximalIdeal R ^ (r - 1) :=
    derivIdeal_le_pow_of_le_pow k hIr
  have h1 : ((r - 1 : ℕ) : ℕ∞) ≤ idealOrder (derivIdeal k I) :=
    (le_idealOrder_iff _ (r - 1)).mpr hle
  have h2 : ¬ (((r - 1) + 1 : ℕ) : ℕ∞) ≤ idealOrder (derivIdeal k I) := by
    intro hc
    have h := (le_idealOrder_iff _ ((r - 1) + 1)).mp hc
    apply hnot
    rw [hx]
    have hrr : (r - 1) + 1 = r := by omega
    rwa [hrr] at h
  exact eq_natCast_of_le_of_not_succ_le (r - 1) _ h1 h2

theorem idealOrder_derivIdealIterate_of_isUnit_natCast (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R)
    (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {I : Ideal R} {r : ℕ} (hI : idealOrder I = (r : ℕ∞)) {j : ℕ} (hj : j ≤ r) :
    idealOrder (derivIdealIterate k j I) = ((r - j : ℕ) : ℕ∞) := by
  revert hj
  induction j with
  | zero =>
      intro _
      rw [derivIdealIterate_zero, Nat.sub_zero]
      exact hI
  | succ j ih =>
      intro hj
      have hj' : j ≤ r := by omega
      have hprev := ih hj'
      have h1 : 1 ≤ r - j := by omega
      have h := idealOrder_derivIdeal_of_isUnit_natCast k x D hD hx hunit h1 hprev
      rw [derivIdealIterate_succ]
      have heq : r - j - 1 = r - (j + 1) := by omega
      rwa [heq] at h

end FunctorialResolution.EmbeddedResolution

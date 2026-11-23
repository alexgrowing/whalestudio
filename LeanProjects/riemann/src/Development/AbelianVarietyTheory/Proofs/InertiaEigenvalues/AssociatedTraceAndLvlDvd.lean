import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr.TraceOnePlusX

variable {l : ℕ} [Fact l.Prime]

theorem dvd_iff_toZMod (x : ℤ_[l]) : (l : ℤ_[l]) ∣ x ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

theorem eq_one_of_pow_eq_one (hl : l ≠ 2) (x : ℤ_[l]) (n : ℕ) (hn : n ≠ 0) (hx : x ^ n = 1)
    (h1 : PadicInt.toZMod x = 1) : x = 1 := by
  have hp : l.Prime := Fact.out
  have hP : Prime (l : ℤ_[l]) := PadicInt.prime_p
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hp.ne_one
  have hd : (l : ℤ_[l]) ∣ x - 1 := by rw [dvd_iff_toZMod, map_sub, h1]; simp
  have hnd : ¬ (l : ℤ_[l]) ∣ x := by rw [dvd_iff_toZMod, h1]; simp
  have e1 := emultiplicity_pow_prime_pow_sub_pow_prime_pow hP (hp.odd_of_ne_two hl) hd hnd k
  have hd2 : (l : ℤ_[l]) ∣ x ^ l ^ k - 1 := by rw [dvd_iff_toZMod, map_sub, map_pow, h1]; simp
  have hnd2 : ¬ (l : ℤ_[l]) ∣ x ^ l ^ k := by rw [dvd_iff_toZMod, map_pow, h1]; simp
  have hm2 : ¬ (l : ℤ_[l]) ∣ (m : ℤ_[l]) := by
    rw [dvd_iff_toZMod, map_natCast, ZMod.natCast_eq_zero_iff]; exact hm
  have e2 := emultiplicity_pow_sub_pow_of_prime hP hd2 hnd2 hm2
  rw [← pow_mul, hx, one_pow, sub_self, emultiplicity_zero] at e2
  rw [one_pow, ← e2] at e1
  by_contra hne
  have hf : FiniteMultiplicity (l : ℤ_[l]) (x - 1) :=
    FiniteMultiplicity.of_prime_left hP (sub_ne_zero.2 hne)
  rw [hf.emultiplicity_eq_multiplicity] at e1
  exact absurd e1.symm (by exact_mod_cast ENat.coe_ne_top _)

theorem toZMod_unit_ne_zero (u : ℤ_[l]ˣ) : PadicInt.toZMod (u : ℤ_[l]) ≠ 0 :=
  (u.isUnit.map _).ne_zero

theorem unit_eq_one (hl : l ≠ 2) (u : ℤ_[l]ˣ) (hu : IsOfFinOrder u)
    (h1 : PadicInt.toZMod (u : ℤ_[l]) = 1) : u = 1 := by
  obtain ⟨n, hn, h⟩ := hu.exists_pow_eq_one
  apply Units.ext
  exact eq_one_of_pow_eq_one hl _ n hn.ne' (by rw [← Units.val_pow_eq_pow_val, h]; rfl) h1

theorem torsion_inj (hl : l ≠ 2) (u v : ℤ_[l]ˣ) (hu : IsOfFinOrder u) (hv : IsOfFinOrder v)
    (h : PadicInt.toZMod (u : ℤ_[l]) = PadicInt.toZMod (v : ℤ_[l])) : u = v := by
  have := unit_eq_one hl (u * v⁻¹) (hu.mul hv.inv) (by
    rw [Units.val_mul, map_mul, h, ← map_mul, ← Units.val_mul, mul_inv_cancel]; simp)
  exact mul_inv_eq_one.1 this

theorem pow_sub_one_eq_one (hl : l ≠ 2) (u : ℤ_[l]ˣ) (hu : IsOfFinOrder u) : u ^ (l - 1) = 1 :=
  unit_eq_one hl _ hu.pow (by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact ZMod.pow_card_sub_one_eq_one (toZMod_unit_ne_zero u))

theorem image_eq (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) :
    D.image (fun δ : ℤ_[l]ˣ => PadicInt.toZMod (δ : ℤ_[l])) = Finset.univ.erase 0 := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.1 hx
    simp [toZMod_unit_ne_zero]
  · rw [Finset.card_image_of_injOn (fun u hu v hv h => torsion_inj hl u v (hD u hu) (hD v hv) h),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card, hc]

theorem mem_of_torsion (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) (u : ℤ_[l]ˣ) (hu : IsOfFinOrder u) : u ∈ D := by
  have : PadicInt.toZMod (u : ℤ_[l]) ∈
      D.image (fun δ : ℤ_[l]ˣ => PadicInt.toZMod (δ : ℤ_[l])) := by
    rw [image_eq D hl hc hD]; simp [toZMod_unit_ne_zero]
  obtain ⟨δ, hδ, h⟩ := Finset.mem_image.1 this
  rwa [← torsion_inj hl δ u (hD δ hδ) hu h]

theorem sum_pow_eq_zero (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) (i : ℕ) (hi : i ≠ 0) (hi2 : i < l - 1) :
    ∑ δ ∈ D, (δ : ℤ_[l]) ^ i = 0 := by
  classical
  let G : Subgroup ℤ_[l]ˣ := CommGroup.torsion ℤ_[l]ˣ
  have hG : ∀ x, x ∈ D ↔ x ∈ G := fun x => ⟨hD x, mem_of_torsion D hl hc hD x⟩
  letI : Fintype G := Fintype.ofFinset D (fun x => hG x)
  have hcard : Fintype.card G = D.card := Fintype.card_of_subtype D hG
  rw [Finset.sum_subtype D hG (F := inferInstance) (fun δ : ℤ_[l]ˣ => (δ : ℤ_[l]) ^ i)]
  exact FiniteField.sum_subgroup_pow_eq_zero hi (by omega)

theorem sum_eval (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) (P : Polynomial ℤ_[l]) (hP : P.natDegree < l)
    (h0 : P.coeff 0 = 0) :
    ∑ δ ∈ D, P.eval (δ : ℤ_[l]) = ((l - 1 : ℕ) : ℤ_[l]) * P.coeff (l - 1) := by
  have hp : l.Prime := Fact.out
  have := hp.two_le
  simp_rw [Polynomial.eval_eq_sum_range' hP]
  rw [Finset.sum_comm, Finset.sum_eq_single (l - 1)]
  · rw [← Finset.mul_sum, mul_comm, Finset.sum_congr rfl (g := fun _ => (1 : ℤ_[l]))]
    · simp [hc]
    · intro δ hδ
      rw [← Units.val_pow_eq_pow_val, pow_sub_one_eq_one hl δ (hD δ hδ)]; rfl
  · intro i hi hne
    rw [← Finset.mul_sum]
    by_cases hi0 : i = 0
    · rw [hi0, h0, zero_mul]
    · rw [sum_pow_eq_zero D hl hc hD i hi0 (by have := Finset.mem_range.1 hi; omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

theorem factorial_mul_choose (c : ℤ_[l]) (k : ℕ) :
    (k.factorial : ℤ_[l]) * Ring.choose c k = (descPochhammer ℤ_[l] k).eval c := by
  rw [← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose, ← Polynomial.aeval_eq_smeval,
    ← descPochhammer_map (algebraMap ℤ ℤ_[l]), Polynomial.eval_map_algebraMap]

theorem factorial_mul_sum_choose (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) (k : ℕ) (hk : k ≠ 0) (hk2 : k < l) :
    (k.factorial : ℤ_[l]) * ∑ δ ∈ D, Ring.choose (δ : ℤ_[l]) k =
      ((l - 1 : ℕ) : ℤ_[l]) * (descPochhammer ℤ_[l] k).coeff (l - 1) := by
  rw [Finset.mul_sum]
  simp_rw [factorial_mul_choose]
  apply sum_eval D hl hc hD
  · rwa [descPochhammer_natDegree]
  · rw [Polynomial.coeff_zero_eq_eval_zero]; exact descPochhammer_ne_zero_eval_zero _ hk

theorem sum_choose_eq_zero (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) (k : ℕ) (hk : k ≠ 0) (hk2 : k < l - 1) :
    ∑ δ ∈ D, Ring.choose (δ : ℤ_[l]) k = 0 := by
  have h := factorial_mul_sum_choose D hl hc hD k hk (by omega)
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [descPochhammer_natDegree]), mul_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast k.factorial_ne_zero)

theorem isUnit_sum_choose (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) : IsUnit (∑ δ ∈ D, Ring.choose (δ : ℤ_[l]) (l - 1)) := by
  have hp : l.Prime := Fact.out
  have := hp.two_le
  have h := factorial_mul_sum_choose D hl hc hD (l - 1) (by omega) (by omega)
  have hm : (descPochhammer ℤ_[l] (l - 1)).coeff (l - 1) = 1 := by
    have := (monic_descPochhammer ℤ_[l] (l - 1)).coeff_natDegree
    rwa [descPochhammer_natDegree] at this
  rw [hm, mul_one] at h
  have hu : IsUnit ((l - 1 : ℕ) : ℤ_[l]) := by
    by_contra hn
    have : ((l - 1 : ℕ) : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  rw [← h] at hu
  exact isUnit_of_mul_isUnit_right hu

end GlobalTheory.CycFr.TraceOnePlusX

namespace GlobalTheory.CycFr

open TraceOnePlusX

theorem associated_trace_and_lvl_dvd {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] [Algebra ℤ_[l] O] (D : Finset ℤ_[l]ˣ) (hl : l ≠ 2) (hc : D.card = l - 1)
    (hD : ∀ δ ∈ D, IsOfFinOrder δ) :
    Associated (1 - (l : O⟦X⟧) + ∑ δ ∈ D, act O (δ : ℤ_[l]) (1 + X)) (X ^ (l - 1)) ∧
      lvl l O 0 ∣ 1 + ∑ δ ∈ D, act O (δ : ℤ_[l]) (1 + X) := by
  have hp : l.Prime := Fact.out
  have h2 := hp.two_le
  simp_rw [act_one_add_X]
  constructor
  · have hco : ∀ k, k ≠ 0 → coeff k (1 - (l : O⟦X⟧) + ∑ δ ∈ D, bin O (δ : ℤ_[l])) =
        algebraMap ℤ_[l] O (∑ δ ∈ D, Ring.choose (δ : ℤ_[l]) k) := by
      intro k hk
      have e : (1 - (l : O⟦X⟧)) = C (1 - (l : O)) := by simp
      rw [e, map_add, coeff_C, if_neg hk, zero_add, map_sum, map_sum]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [binomialSeries_coeff, Algebra.smul_def, mul_one]
    obtain ⟨g, hg⟩ : (X : O⟦X⟧) ^ (l - 1) ∣ 1 - (l : O⟦X⟧) + ∑ δ ∈ D, bin O (δ : ℤ_[l]) := by
      rw [X_pow_dvd_iff]
      intro m hm
      by_cases h0 : m = 0
      · subst h0
        simp [bin, binomialSeries_constantCoeff, hc, Nat.cast_sub hp.one_le]
      · rw [hco m h0, sum_choose_eq_zero D hl hc hD m h0 hm, map_zero]
    have hu : IsUnit g := by
      rw [PowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply,
        ← coeff_X_pow_mul g (l - 1) 0, ← hg, zero_add, hco _ (by omega)]
      exact (isUnit_sum_choose D hl hc hD).map _
    rw [hg]
    exact associated_mul_unit_left _ _ hu
  · have hq : lvl l O 0 ∣ (1 + X : O⟦X⟧) ^ l ^ 1 - 1 := Dvd.intro_left _ (mul_lvl 0)
    have h1 : lvl l O 0 ∣ ∑ δ ∈ D, (bin O (δ : ℤ_[l]) -
        (1 + X) ^ (PadicInt.toZMod (δ : ℤ_[l])).val) := by
      refine Finset.dvd_sum fun δ _ => hq.trans ?_
      rw [← bin_nat (l := l) (PadicInt.toZMod (δ : ℤ_[l])).val]
      apply dvd_bin_sub
      rw [pow_one, dvd_iff_toZMod, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    have h3 : 1 + ∑ δ ∈ D, (1 + X : O⟦X⟧) ^ (PadicInt.toZMod (δ : ℤ_[l])).val = lvl l O 0 := by
      rw [← Finset.sum_image (s := D) (g := fun δ : ℤ_[l]ˣ => PadicInt.toZMod (δ : ℤ_[l]))
        (f := fun x : ZMod l => (1 + X : O⟦X⟧) ^ x.val)
        (fun u hu v hv h => torsion_inj hl u v (hD u hu) (hD v hv) h), image_eq D hl hc hD]
      have := Finset.add_sum_erase Finset.univ (fun x : ZMod l => (1 + X : O⟦X⟧) ^ x.val)
        (Finset.mem_univ 0)
      simp only [ZMod.val_zero, pow_zero] at this
      rw [this, lvl]
      simp only [pow_zero, pow_one]
      refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
      · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
      · intro x _ y _ h; exact ZMod.val_injective l h
      · intro i hi; exact ⟨(i : ZMod l), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hi)⟩
      · intro x _; rfl
    rw [Finset.sum_sub_distrib] at h1
    have := dvd_add h1 (dvd_refl _)
    convert this using 1
    rw [← h3]; ring

end GlobalTheory.CycFr

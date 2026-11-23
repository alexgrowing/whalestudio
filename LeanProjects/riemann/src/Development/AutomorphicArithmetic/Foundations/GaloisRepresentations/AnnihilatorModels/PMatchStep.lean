import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private lemma coeff_lin_form {A ι : Type} [CommRing A] [Fintype ι] (a : ι → A) (k₀ : ι) :
    MvPolynomial.coeff (Finsupp.single k₀ 1) (∑ k, MvPolynomial.C (a k) * MvPolynomial.X k : MvPolynomial ι A) = a k₀ := by
  classical
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  rw [Finset.sum_eq_single k₀]
  · simp
  · intro k _ hk
    rw [MvPolynomial.coeff_X', if_neg, mul_zero]
    intro h
    exact hk (Finsupp.single_left_injective one_ne_zero h)
  · simp

theorem UpperTheory.Gal.crystallineComparison.matchStep_of :
    GaussLin → SameNormBasic → LinFactor → MatchStep := by
  intro hG hS hL B _ ϖ hϖ hnu ι _ N m hm u u' hcard hsame x hx hchain hdich
  by_contra hcon
  push_neg at hcon
  have hex : ∀ y : ι → B, ∃ c : B, ∃ e : ι → B,
      y ∈ u' → c ∣ ϖ ^ m ∧ (∃ k₀, e k₀ = 1) ∧ ∀ k, x k - y k = c * e k := by
    intro y
    by_cases hy : y ∈ u'
    · obtain ⟨k, hk⟩ := hcon y hy
      have hdk : x k - y k ∣ ϖ ^ m := (hdich y hy k).resolve_right hk
      obtain ⟨c, e, k₀, hc, he, hd⟩ := hL B ι (ϖ ^ m) (fun k => x k - y k) ⟨k, hdk⟩ (hchain y hy)
      exact ⟨c, e, fun _ => ⟨hc, ⟨k₀, he⟩, hd⟩⟩
    · exact ⟨0, 0, fun h => absurd h hy⟩
  choose c e hce using hex
  set M := ϖ ^ (m * (N + 1)) with hM
  have h4 := (hS (B ⧸ Ideal.span {M}) ι).2.2.2 (fun k => Ideal.Quotient.mk (Ideal.span {M}) (x k))
    (redMod M u) (redMod M u') hsame (Multiset.mem_map_of_mem _ hx)
  let L : (ι → B) → MvPolynomial ι (B ⧸ Ideal.span {M}) :=
    fun y => ∑ k, MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (e y k)) * MvPolynomial.X k
  have h4' : (u'.map (fun y => MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (c y)) * L y)).prod = 0 := by
    rw [← h4]
    congr 1
    unfold redMod
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun y hy => ?_
    simp only [Function.comp, L, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_sub, (hce y hy).2.2 k, map_mul, map_mul, mul_assoc]
  rw [Multiset.prod_map_mul] at h4'
  have hC : (u'.map fun y => (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (c y)) :
        MvPolynomial ι (B ⧸ Ideal.span {M}))).prod =
      (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {M}) (u'.map c).prod) :
        MvPolynomial ι (B ⧸ Ideal.span {M})) := by
    rw [map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    rfl
  rw [hC] at h4'
  have hz : Ideal.Quotient.mk (Ideal.span {M}) (u'.map c).prod = 0 := by
    refine hG _ ι _ (u'.map L) ?_ h4'
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hp
    obtain ⟨k₀, hk₀⟩ := (hce y hy).2.1
    exact ⟨Finsupp.single k₀ 1, by simp only [L]; rw [coeff_lin_form, hk₀, map_one]⟩
  have hdvd : M ∣ (u'.map c).prod :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hdvd2 : (u'.map c).prod ∣ (ϖ ^ m) ^ Multiset.card u' := by
    have hh := Multiset.prod_dvd_prod_of_dvd (S := u') c (fun _ => ϖ ^ m) (fun y hy => (hce y hy).1)
    simpa [Multiset.map_const', Multiset.prod_replicate] using hh
  obtain ⟨t, ht⟩ := hdvd.trans hdvd2
  have hr : M = (ϖ ^ m) ^ Multiset.card u' * ϖ ^ (m * (N + 1 - Multiset.card u')) := by
    rw [hM, ← pow_mul, ← pow_add, ← Nat.mul_add]
    congr 2
    omega
  rw [hr, mul_assoc] at ht
  have hpa : (ϖ ^ m) ^ Multiset.card u' ∈ nonZeroDivisors B := pow_mem (pow_mem hϖ m) _
  have h0 : (ϖ ^ (m * (N + 1 - Multiset.card u')) * t - 1) * (ϖ ^ m) ^ Multiset.card u' = 0 := by
    linear_combination -ht
  have h1 : ϖ ^ (m * (N + 1 - Multiset.card u')) * t = 1 :=
    sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hpa).2 _ h0)
  have hu : IsUnit (ϖ ^ (m * (N + 1 - Multiset.card u'))) := isUnit_iff_exists_inv.mpr ⟨t, h1⟩
  exact hnu ((isUnit_pow_iff (Nat.mul_ne_zero (by omega) (by omega))).mp hu)

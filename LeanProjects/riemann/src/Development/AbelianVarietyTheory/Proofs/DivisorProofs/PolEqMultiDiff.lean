import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMvPolynomialOfIteratedBackwardDifferenceVa

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.ArInt

namespace GlobalTheory.FibreProj

variable {ι : Type} [Fintype ι]

open Classical in

def pol (φ : (ι → ℤ) → ℝ) : ℝ := ∑ S : Finset ι, (-1 : ℝ) ^ S.card * φ fun i => if i ∈ S then -1 else 0

theorem pol_eq_multiDiff [DecidableEq ι] (φ : (ι → ℤ) → ℝ) :
    pol φ = multiDiff (fun i => (Pi.single i 1 : ι → ℤ)) φ 0 := by
  rw [pol, multiDiff_apply]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [zsmul_eq_mul]
  push_cast
  congr 2
  funext i
  simp only [zero_sub, Pi.neg_apply, Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  split_ifs <;> simp

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in

theorem _root_.GlobalTheory.FibreProj.pol_sum {J : Type} (T : Finset J)
    (φ : J → (ι → ℤ) → ℝ) :
    _root_.GlobalTheory.FibreProj.pol (fun n => ∑ j ∈ T, φ j n) =
      ∑ j ∈ T, _root_.GlobalTheory.FibreProj.pol (φ j) := by
  unfold _root_.GlobalTheory.FibreProj.pol
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem pol_sub (φ ψ : (ι → ℤ) → ℝ) : pol (fun n => φ n - ψ n) = pol φ - pol ψ := by
  simp only [pol, mul_sub, Finset.sum_sub_distrib]

theorem pol_const_mul (a : ℝ) (φ : (ι → ℤ) → ℝ) : pol (fun n => a * φ n) = a * pol φ := by
  simp only [pol, Finset.mul_sum, mul_left_comm]

theorem pol_mul_const (a : ℝ) (φ : (ι → ℤ) → ℝ) : pol (fun n => φ n * a) = pol φ * a := by
  simp only [pol, Finset.sum_mul, mul_assoc]

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
private theorem sum_pow_eq_sum_words_prod {R : Type} [CommRing R] (c : ι → R) (D : ℕ) :
    (∑ i, c i) ^ D = ∑ f : Fin D → ι, ∏ k, c (f k) := by
  rw [← Fin.prod_const, Fintype.prod_sum]

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_neg_one_pow_card_range_subset_eq_ite_surjective {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (f : Fin D → ι) :
    ∑ S : Finset ι, (-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0) =
      if Function.Surjective f then (-1) ^ D else 0 := by
  have hr : ∀ t : Finset ι, (∏ i ∈ t, (-1 : R)) *
      ∏ i ∈ Finset.univ \ t, (if i ∉ Set.range f then (1 : R) else 0) =
        (-1) ^ t.card * (if ∀ k, f k ∈ t then 1 else 0) := by
    intro t
    rw [Finset.prod_const, Finset.prod_ite_zero, Finset.prod_const_one]
    have hiff : (∀ i ∈ Finset.univ \ t, i ∉ Set.range f) ↔ ∀ k, f k ∈ t := by
      constructor
      · intro h k
        by_contra hk
        exact h (f k) (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hk⟩) ⟨k, rfl⟩
      · rintro h i hi ⟨k, rfl⟩
        exact (Finset.mem_sdiff.1 hi).2 (h k)
    simp only [hiff]
  calc ∑ S : Finset ι, (-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0)
      = ∑ t ∈ (Finset.univ : Finset ι).powerset, (∏ i ∈ t, (-1 : R)) *
          ∏ i ∈ Finset.univ \ t, (if i ∉ Set.range f then (1 : R) else 0) := by
        rw [Finset.powerset_univ]
        exact Finset.sum_congr rfl fun t _ => (hr t).symm
    _ = ∏ i, ((-1 : R) + if i ∉ Set.range f then 1 else 0) := (Finset.prod_add _ _ _).symm
    _ = _ := by
        split_ifs with hs
        · have h1 : ∀ i, ((-1 : R) + if i ∉ Set.range f then 1 else 0) = -1 := fun i => by
            rw [if_neg (show ¬(i ∉ Set.range f) from not_not.2 (hs i)), add_zero]
          simp only [h1, Finset.prod_const, Finset.card_univ, hD]
        · simp only [Function.Surjective, not_forall] at hs
          obtain ⟨i, hi⟩ := hs
          exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos (show i ∉ Set.range f from fun h => hi h)]; ring)

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_surjective_words_prod_eq_factorial_prod {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (w : ι → R) :
    ∑ f : Fin D → ι, (∏ k, w (f k)) * (if Function.Surjective f then (-1 : R) ^ D else 0) =
      (-1) ^ D * D.factorial * ∏ i, w i := by
  have hbij : ∀ f : Fin D → ι, Function.Surjective f → Function.Bijective f := fun f hf =>
    (Fintype.bijective_iff_surjective_and_card f).2 ⟨hf, by rw [Fintype.card_fin, hD]⟩
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have hprod : ∀ f ∈ Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f),
      (∏ k, w (f k)) * (-1 : R) ^ D = (∏ i, w i) * (-1) ^ D := by
    intro f hf
    rw [← Equiv.prod_comp (Equiv.ofBijective f (hbij f (Finset.mem_filter.1 hf).2)) w]
    rfl
  have e : Fin D ≃ ι := (Fintype.equivFinOfCardEq hD).symm
  have hcard : (Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f)).card =
      D.factorial := by
    calc (Finset.univ.filter (fun f : Fin D → ι => Function.Surjective f)).card
        = (Finset.univ.map ⟨fun σ : Fin D ≃ ι => (σ : Fin D → ι),
            DFunLike.coe_injective⟩).card := by
          congr 1
          ext f
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Function.Embedding.coeFn_mk]
          constructor
          · intro hf
            exact ⟨Equiv.ofBijective f (hbij f hf), rfl⟩
          · rintro ⟨σ, rfl⟩
            exact σ.surjective
      _ = Fintype.card (Fin D ≃ ι) := by rw [Finset.card_map, Finset.card_univ]
      _ = D.factorial := by rw [Fintype.card_equiv e, Fintype.card_fin]
  rw [Finset.sum_congr rfl hprod, Finset.sum_const, hcard, nsmul_eq_mul]
  ring

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in
private theorem sum_neg_one_pow_card_mul_sum_pow_eq_factorial_prod {R : Type} [CommRing R] {D : ℕ}
    (hD : Fintype.card ι = D) (w : ι → R) :
    ∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then w i else 0) ^ D =
      (-1) ^ D * D.factorial * ∏ i, w i := by
  calc ∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then w i else 0) ^ D
      = ∑ S : Finset ι, ∑ f : Fin D → ι,
          (∏ k, w (f k)) * ((-1 : R) ^ S.card * (if ∀ k, f k ∈ S then 1 else 0)) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [sum_pow_eq_sum_words_prod, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.prod_ite_zero]
        simp only [Finset.mem_univ, true_implies]
        split_ifs <;> ring
    _ = ∑ f : Fin D → ι, (∏ k, w (f k)) *
          (if Function.Surjective f then (-1 : R) ^ D else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Finset.mul_sum, sum_neg_one_pow_card_range_subset_eq_ite_surjective hD f]
    _ = _ := sum_surjective_words_prod_eq_factorial_prod hD w

set_option autoImplicit false in
open MvPolynomial in
variable {ι : Type} [Fintype ι] in
open Classical in

theorem _root_.GlobalTheory.FibreProj.pol_pow {R : Type} [CommRing R]
    [Algebra ℝ R] (z : ι → R) (Φ : R →ₗ[ℝ] ℝ) {D : ℕ} (hD : Fintype.card ι = D) :
    _root_.GlobalTheory.FibreProj.pol (fun n => Φ ((∑ i, (n i : ℝ) • z i) ^ D)) =
      D.factorial * Φ (∏ i, z i) := by
  unfold _root_.GlobalTheory.FibreProj.pol
  have hsum : ∀ S : Finset ι, (∑ i, (((if i ∈ S then -1 else 0 : ℤ) : ℝ)) • z i) =
      ∑ i, if i ∈ S then -z i else 0 := by
    intro S
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp only [hsum]
  have hterm : ∀ (k : ℕ) (x : R), Φ ((-1 : R) ^ k * x) = (-1 : ℝ) ^ k * Φ x := by
    intro k x
    rw [← smul_eq_mul ((-1 : ℝ) ^ k), ← map_smul, Algebra.smul_def, map_pow, map_neg, map_one]
  have h1 : ((-1 : R) ^ D) * (-1) ^ D = 1 := by rw [← mul_pow]; simp
  have hfinal : Φ ((-1 : R) ^ D * D.factorial * ∏ i, -z i) = D.factorial * Φ (∏ i, z i) := by
    rw [Finset.prod_neg, Finset.card_univ, hD]
    calc Φ ((-1) ^ D * D.factorial * ((-1) ^ D * ∏ i, z i))
        = Φ ((D.factorial : ℝ) • ∏ i, z i) := by
          congr 1
          rw [Algebra.smul_def, map_natCast]
          linear_combination (↑D.factorial * ∏ i, z i) * h1
      _ = _ := by rw [map_smul, smul_eq_mul]
  calc ∑ S : Finset ι, (-1 : ℝ) ^ S.card * Φ ((∑ i, if i ∈ S then -z i else 0) ^ D)
      = Φ (∑ S : Finset ι, (-1 : R) ^ S.card * (∑ i, if i ∈ S then -z i else 0) ^ D) := by
        rw [map_sum]
        simp only [hterm]
    _ = Φ ((-1 : R) ^ D * D.factorial * ∏ i, -z i) :=
        congrArg Φ (sum_neg_one_pow_card_mul_sum_pow_eq_factorial_prod hD fun i => -z i)
    _ = _ := hfinal

theorem pol_lin_pow (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) {D : ℕ} (hD : Fintype.card ι = D) :
    pol (fun n : ι → ℤ => Φ (lin (fun i => (n i : ℝ)) ^ D)) = D.factorial * Φ (∏ i, X i) := by
  simpa only [lin, smul_eq_C_mul] using pol_pow (fun i => (X i : MvPolynomial ι ℝ)) Φ hD

theorem pol_mix (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ) {D : ℕ} (hD : Fintype.card ι = D) :
    pol (fun n : ι → ℤ => Φ (X none * rename some (lin fun i => (n i : ℝ)) ^ D)) =
      D.factorial * Φ (∏ o, X o) := by
  have := pol_lin_pow (Φ ∘ₗ LinearMap.mulLeft ℝ (X none) ∘ₗ
    (rename some : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial (Option ι) ℝ).toLinearMap) hD
  simpa [Fintype.prod_option] using this

end GlobalTheory.FibreProj

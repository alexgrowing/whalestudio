import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFreeStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc.FrobIdeal

theorem exists_coords_mem {R ι : Type} [CommRing R] [Fintype ι] (f : R →+* R) (e : ι → R)
    (hspan : ∀ y : R, ∃ z : ι → R, y = ∑ j, e j * f (z j)) (𝔟 : Ideal R) {x : R} (hx : x ∈ 𝔟.map f) :
    ∃ w : ι → R, (∀ j, w j ∈ 𝔟) ∧ x = ∑ j, e j * f (w j) := by
  have key : ∀ a : R, ∃ w : ι → R, (∀ j, w j ∈ 𝔟) ∧ a * x = ∑ j, e j * f (w j) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      intro a
      obtain ⟨z, rfl⟩ := hspan a
      refine ⟨fun j => z j * t, fun j => 𝔟.mul_mem_left _ ht, ?_⟩
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, mul_assoc]
    | zero => exact fun a => ⟨0, fun _ => 𝔟.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      intro a
      obtain ⟨u, hu, h1⟩ := hx a
      obtain ⟨v, hv, h2⟩ := hy a
      refine ⟨u + v, fun j => 𝔟.add_mem (hu j) (hv j), ?_⟩
      rw [mul_add, h1, h2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, map_add, mul_add]
    | smul c x _ hx =>
      intro a
      obtain ⟨u, hu, h1⟩ := hx (a * c)
      exact ⟨u, hu, by rw [← h1, smul_eq_mul, mul_assoc]⟩
  simpa using key 1

theorem colon_le_map {R ι : Type} [CommRing R] [Fintype ι] (f : R →+* R) (e : ι → R)
    (hfree : ∀ y : R, ∃! z : ι → R, y = ∑ j, e j * f (z j)) (𝔞 𝔟 : Ideal R) (x q : R)
    (hx : f x = x * q) (hq : ∀ g ∈ 𝔞, q * g ∈ 𝔟.map f) {y : R} (hy : x * y ∈ 𝔞) :
    ∃ z : ι → R, (∀ j, x * z j ∈ 𝔟) ∧ y = ∑ j, e j * f (z j) := by
  obtain ⟨z, hz, -⟩ := hfree y
  refine ⟨z, ?_, hz⟩
  obtain ⟨w, hw, h⟩ := exists_coords_mem f e (fun y => (hfree y).exists) 𝔟 (hq _ hy)
  have h2 : q * (x * y) = ∑ j, e j * f (x * z j) := by
    conv_lhs => rw [hz]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hx]; ring
  have h3 : (fun j => x * z j) = w := (hfree _).unique h2 h
  intro j
  have : x * z j = w j := congrFun h3 j
  rw [this]; exact hw j

theorem phi_mem_span (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ϖ : O)
    (hϖ : ϖ ∣ (l : O)) (N : ℕ) (hN : 1 ≤ N) {y : PowerSeries O}
    (hy : y ∈ Ideal.span {PowerSeries.C ϖ, PowerSeries.X ^ N}) :
    phi l O y ∈ Ideal.span {PowerSeries.C ϖ, PowerSeries.X ^ (N + 1)} := by
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hy
  obtain ⟨r, hr⟩ := Series.phi_X_mod l O
  obtain ⟨t, ht⟩ := hϖ
  have hC : phi l O (PowerSeries.C ϖ) = PowerSeries.C ϖ := (phi l O).commutes ϖ
  have hl : (l : PowerSeries O) = PowerSeries.C ϖ * PowerSeries.C t := by
    rw [← map_mul, ← ht, map_natCast]
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow (phi l O PowerSeries.X) (PowerSeries.X ^ l) N
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨m, hm⟩ : ∃ m, l * N = m + (N + 1) := ⟨l * N - (N + 1), by
    have : 2 * N ≤ l * N := Nat.mul_le_mul_right N h2
    omega⟩
  rw [← pow_mul, hm, pow_add] at hd
  nth_rewrite 2 [hr] at hd
  rw [hl] at hd
  refine Ideal.mem_span_pair.2 ⟨phi l O a + phi l O b * PowerSeries.C t * r * d,
    phi l O b * PowerSeries.X ^ m, ?_⟩
  rw [map_add, map_mul, map_mul, map_pow, hC]
  linear_combination (-(phi l O b)) * hd

end GlobalTheory.Cyc.FrobIdeal

namespace GlobalTheory.Cyc

open FrobIdeal

theorem XX_pow_mem_of_QQ_pow_mul_mem_map_phi : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (s n H c : ℕ) [NeZero n], 1 ≤ s → ∀ 𝔞 : ZMod n → Ideal (PowerSeries O), (∀ i, PowerSeries.X ^ c ∈ 𝔞 i) → (∀ i, ∀ g ∈ 𝔞 i, QQ l O s ^ H * g ∈ (𝔞 (i - 1)).map (phi l O)) → ∀ i, XX l O s ^ H ∈ 𝔞 i := by
  intro l _ O _ _ _ _ _ hl0 hlu s n H c _ _ 𝔞 hc hK i
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ∀ a : O, ¬ IsUnit a → ϖ ∣ a := fun a ha => by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact ha
  by_contra hi
  have main : ∀ (m : ℕ) (y : PowerSeries O), XX l O s ^ H * y ∈ 𝔞 (i + m) →
      y ∈ Ideal.span {PowerSeries.C ϖ, PowerSeries.X ^ (m + 1)} := by
    intro m
    induction m with
    | zero =>
      intro y hy
      rw [Nat.cast_zero, add_zero] at hy
      have hu : ¬ IsUnit y := fun hu => hi ((Ideal.mul_unit_mem_iff_mem _ hu).1 hy)
      rw [PowerSeries.isUnit_iff_constantCoeff] at hu
      obtain ⟨t, ht⟩ := hdvd _ hu
      refine Ideal.mem_span_pair.2 ⟨PowerSeries.C t, PowerSeries.mk fun p => PowerSeries.coeff (p + 1) y, ?_⟩
      conv_rhs => rw [PowerSeries.eq_shift_mul_X_add_const y]
      rw [ht, map_mul]; ring
    | succ m ih =>
      intro y hy
      obtain ⟨z, hz, rfl⟩ := colon_le_map (phi l O : PowerSeries O →+* PowerSeries O)
        (fun j : Fin l => (1 + PowerSeries.X) ^ (j : ℕ)) (GlobalTheory.T.existsUnique_decomposition_one_add_X_pow_mul_phi l O hl0 hlu)
        (𝔞 (i + (m + 1 : ℕ))) (𝔞 (i + m)) (XX l O s ^ H) (QQ l O s ^ H)
        (by rw [map_pow, ← mul_pow]; exact congrArg (· ^ H) (Series.phi_XX l O s))
        (fun g hg => by
          have h := hK _ g hg
          rw [Nat.cast_succ, ← add_assoc, add_sub_cancel_right] at h
          exact h) hy
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _
        (phi_mem_span l O ϖ (hdvd _ hlu) (m + 1) (Nat.le_add_left 1 m) (ih _ (hz j)))
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (main c _ (Ideal.mul_mem_left _ _ (hc _)))
  have h := congrArg (PowerSeries.coeff c) hab
  rw [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', if_neg (by omega),
    PowerSeries.coeff_X_pow, if_pos rfl, add_zero] at h
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one_right _ h)

end GlobalTheory.Cyc

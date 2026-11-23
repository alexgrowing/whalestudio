import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEnStatement
open scoped PowerSeries Pointwise

namespace GlobalTheory.FrobIdealDeg

open PowerSeries

variable {O : Type} [CommRing O] (l : ℕ) (hl : 2 ≤ l) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
  (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) =
    if l ∣ m then PowerSeries.coeff (m / l) f else 0)

noncomputable def comps (f : O⟦X⟧) : Fin l → O⟦X⟧ :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).exists.choose

include hφ in
lemma comps_spec (f : O⟦X⟧) :
    f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (comps l hl φ hφ f j) :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).exists.choose_spec

lemma comps_eq {f : O⟦X⟧} {c : Fin l → O⟦X⟧}
    (h : f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (c j)) : comps l hl φ hφ f = c :=
  (GlobalTheory.T.powerSeries_existsUnique_decomp_over_frobeniusLike_endo l hl φ hφ f).unique (comps_spec l hl φ hφ f) h

lemma comps_add (f f' : O⟦X⟧) :
    comps l hl φ hφ (f + f') = comps l hl φ hφ f + comps l hl φ hφ f' := by
  apply comps_eq
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  rw [← comps_spec l hl φ hφ f, ← comps_spec l hl φ hφ f']

lemma comps_zero : comps l hl φ hφ (0 : O⟦X⟧) = 0 := by
  apply comps_eq
  simp

lemma comps_mul_phi (c f : O⟦X⟧) (k : Fin l) :
    comps l hl φ hφ (φ c * f) k = c * comps l hl φ hφ f k := by
  have : comps l hl φ hφ (φ c * f) = fun k => c * comps l hl φ hφ f k := by
    apply comps_eq
    conv_lhs => rw [comps_spec l hl φ hφ f]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  rw [this]

include hl hφ in
lemma phi_X : φ PowerSeries.X = PowerSeries.X ^ l := by
  ext m
  rw [hφ, PowerSeries.coeff_X_pow]
  by_cases h1 : l ∣ m
  · obtain ⟨q, rfl⟩ := h1
    rw [if_pos (dvd_mul_right l q), Nat.mul_div_cancel_left q (by omega), PowerSeries.coeff_X]
    by_cases hq : q = 1
    · subst hq; simp
    · rw [if_neg hq, if_neg]
      intro h2
      apply hq
      have : l * q = l * 1 := by simpa using h2
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
  · rw [if_neg h1, if_neg]
    rintro rfl
    exact h1 dvd_rfl

lemma comps_X_pow (t : ℕ) :
    comps l hl φ hφ (PowerSeries.X ^ t) ⟨t % l, Nat.mod_lt _ (Nat.lt_of_lt_of_le (by norm_num) hl)⟩ =
      PowerSeries.X ^ (t / l) := by
  have : comps l hl φ hφ (PowerSeries.X ^ t) = fun j =>
      if j = (⟨t % l, Nat.mod_lt _ (Nat.lt_of_lt_of_le (by norm_num) hl)⟩ : Fin l) then PowerSeries.X ^ (t / l) else 0 := by
    apply comps_eq
    simp only [apply_ite φ, map_zero, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [map_pow, phi_X l hl φ hφ, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [this]; simp

lemma descend (J : Ideal O⟦X⟧) (b : ℕ) (f : O⟦X⟧)
    (hf : f ∈ J.map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) (k : Fin l) :
    comps l hl φ hφ f k ∈ J ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  clear hf
  rw [comps_add, Pi.add_apply]
  refine Submodule.add_mem_sup ?_ ?_
  · have key : ∀ r : O⟦X⟧, comps l hl φ hφ (r * x) k ∈ J := by
      change x ∈ Submodule.span O⟦X⟧ (φ '' (J : Set O⟦X⟧)) at hx
      induction hx using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, hj, rfl⟩ := hz
        intro r
        rw [mul_comm, comps_mul_phi]
        exact J.mul_mem_right _ hj
      | zero =>
        intro r
        rw [mul_zero, comps_zero]
        exact J.zero_mem
      | add z w _ _ hz hw =>
        intro r
        rw [mul_add, comps_add, Pi.add_apply]
        exact J.add_mem (hz r) (hw r)
      | smul s z _ hz =>
        intro r
        rw [smul_eq_mul, ← mul_assoc]
        exact hz (r * s)
    simpa using key 1
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have e : c * (l : O⟦X⟧) ^ b = φ ((l : O⟦X⟧) ^ b) * c := by
      rw [map_pow, map_natCast, mul_comm]
    rw [e, comps_mul_phi]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

lemma pow_mem_binom (e h b : ℕ) (hb : 1 ≤ b) :
    (PowerSeries.X : O⟦X⟧) ^ (e * (h + b - 1)) ∈
      Ideal.span {(PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h} ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  have : (PowerSeries.X : O⟦X⟧) ^ (e * (h + b - 1)) =
      ((PowerSeries.X ^ e + (l : O⟦X⟧)) + (-(l : O⟦X⟧))) ^ (h + b - 1) := by
    rw [pow_mul]; congr 1; ring
  rw [this]
  apply Ideal.add_pow_mem_of_pow_mem_of_le (m := h) (n := b)
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  · rw [neg_pow]
    exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  · omega

end GlobalTheory.FrobIdealDeg

namespace GlobalTheory

open GlobalTheory.FrobIdealDeg in

theorem frobenius_ideal_degree_bound : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l →
    ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) =
      if l ∣ m then PowerSeries.coeff (m / l) f else 0) →
    ∀ (a e h b : ℕ) [NeZero a] (I : ZMod a → Ideal O⟦X⟧), 1 ≤ b → h + b ≤ l →
    (∀ τ, ∃ s : ℕ, PowerSeries.X ^ s ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b}) →
    (∀ τ, ∀ x ∈ I τ, (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x ∈ (I (τ - 1)).map φ) →
    ∀ τ, (PowerSeries.X : O⟦X⟧) ^ (e * (h + b)) ∈ (I τ).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
  intro O _ l hl φ hφ a e h b _ I hb hhb hs hI
  classical
  have step : ∀ τ t, (PowerSeries.X : O⟦X⟧) ^ t ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} →
      (PowerSeries.X : O⟦X⟧) ^ (t + e * (h + b - 1)) ∈
        (I (τ - 1)).map φ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} := by
    intro τ t ht
    have hK := pow_mem_binom (O := O) l e h b hb
    obtain ⟨r1, hr1, r2, hr2, hr⟩ := Submodule.mem_sup.mp hK
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ht
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr1
    rw [pow_add, ← hxy, ← hr]
    have hring : (x + y) * (c * (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h + r2) =
        c * ((PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h * x) +
          (y * (c * (PowerSeries.X ^ e + (l : O⟦X⟧)) ^ h + r2) + x * r2) := by ring
    rw [hring]
    exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (hI τ x hx))
      (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hy) (Ideal.mul_mem_left _ _ hr2))
  let s : ZMod a → ℕ := fun τ => Nat.find (hs τ)
  have hspec : ∀ τ, (PowerSeries.X : O⟦X⟧) ^ s τ ∈ I τ ⊔ Ideal.span {(l : O⟦X⟧) ^ b} :=
    fun τ => Nat.find_spec (hs τ)
  have down : ∀ τ, l * s τ ≤ s (τ + 1) + e * (h + b - 1) := by
    intro τ
    have h1 := step (τ + 1) (s (τ + 1)) (hspec (τ + 1))
    rw [add_sub_cancel_right] at h1
    have h2 := descend l hl φ hφ (I τ) b _ h1 ⟨(s (τ + 1) + e * (h + b - 1)) % l,
      Nat.mod_lt _ (by omega)⟩
    rw [comps_X_pow] at h2
    have h3 : s τ ≤ (s (τ + 1) + e * (h + b - 1)) / l := Nat.find_min' _ h2
    calc l * s τ ≤ l * ((s (τ + 1) + e * (h + b - 1)) / l) := Nat.mul_le_mul_left _ h3
      _ ≤ s (τ + 1) + e * (h + b - 1) := Nat.mul_div_le _ _
  obtain ⟨τ0, -, hmax⟩ := Finset.exists_max_image Finset.univ s Finset.univ_nonempty
  obtain ⟨n, hn⟩ : ∃ n, h + b - 1 = n := ⟨_, rfl⟩
  have hnl : n + 1 ≤ l := by omega
  have hS : s τ0 ≤ e := by
    have d := down τ0
    have m := hmax (τ0 + 1) (Finset.mem_univ _)
    rw [hn] at d
    by_contra hc
    push_neg at hc
    nlinarith
  intro τ
  have h1 := step (τ + 1) (s (τ + 1)) (hspec (τ + 1))
  rw [add_sub_cancel_right] at h1
  refine Ideal.pow_mem_of_pow_mem _ h1 ?_
  have m := hmax (τ + 1) (Finset.mem_univ _)
  have : e * (h + b) = e * (h + b - 1) + e := by
    rw [← Nat.mul_add_one]; congr 1; omega
  omega

end GlobalTheory

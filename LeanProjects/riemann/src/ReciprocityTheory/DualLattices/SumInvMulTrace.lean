import Mathlib
import ReciprocityTheory.DualLattices.NearIdentityColengthStatement

namespace ReciprocityTheory.PGsh

open Finset

private lemma sum_inv_mul_trace (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F]
    [inst : Algebra (ZMod p) F] :
    ∑ a : F, a⁻¹ * algebraMap (ZMod p) F (Algebra.trace (ZMod p) F a) = -1 := by
  classical
  simp_rw [_root_.trace_eq_sum_automorphisms, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
  have h1 : ∑ a : F, a⁻¹ * (1 : F ≃ₐ[ZMod p] F) a = -1 := by
    have : ∀ a : F, a⁻¹ * (1 : F ≃ₐ[ZMod p] F) a = 1 - if a = 0 then 1 else 0 := by
      intro a
      by_cases h : a = 0
      · simp [h]
      · simp [h]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, nsmul_eq_mul, mul_one,
      FiniteField.cast_card_eq_zero, zero_sub]
  have h2 : ∀ σ : F ≃ₐ[ZMod p] F, σ ≠ 1 → ∑ a : F, a⁻¹ * σ a = 0 := by
    intro σ hσ
    obtain ⟨b, hb⟩ : ∃ b, σ b ≠ b := by
      by_contra h
      push Not at h
      exact hσ (AlgEquiv.ext h)
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hb
    have key : ∑ a : F, (b⁻¹ * σ b) * (a⁻¹ * σ a) = ∑ a : F, a⁻¹ * σ a := by
      refine Fintype.sum_equiv (Equiv.mulLeft₀ b hb0) _ _ (fun a => ?_)
      simp only [Equiv.mulLeft₀_apply, map_mul, mul_inv]
      ring
    rw [← Finset.mul_sum] at key
    have hne : b⁻¹ * σ b ≠ 1 := fun h => hb ((inv_mul_eq_one₀ hb0).mp h).symm
    have : (b⁻¹ * σ b - 1) * ∑ a : F, a⁻¹ * σ a = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  rw [h1, Finset.sum_eq_zero (fun σ hσ => h2 σ (Finset.ne_of_mem_erase hσ)), add_zero]

theorem gaussCongruence : GaussCongruenceStatement := by
  intro p _ F _ _ _ O _ _ m _ ι ω ζ hF hζ hω
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  show ∃ y ∈ m, (∑ a : F, ω⁻¹ a * ζ ^ (Algebra.trace (ZMod p) F a).val) = (ζ - 1) * (y - 1)
  obtain ⟨c, rfl⟩ : ∃ c, ζ = 1 + c := ⟨ζ - 1, by ring⟩
  simp only [add_sub_cancel_left]
  have : CharP (O ⧸ m) p := charP_of_injective_ringHom ι.injective p

  have hc : c ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h : (Ideal.Quotient.mk m c) ^ p = 0 := by
      have e : Ideal.Quotient.mk m c = Ideal.Quotient.mk m (1 + c) - 1 := by
        rw [map_add, map_one]; ring
      rw [e, sub_pow_char, one_pow, ← map_pow, hζ, map_one, sub_self]
    exact pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h

  have hbin : ∀ n : ℕ, ∃ r : O, (1 + c) ^ n = 1 + (n : O) * c + c ^ 2 * r := by
    intro n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨n + r + c * r, by rw [pow_succ, hr]; push_cast; ring⟩
  choose r hr using hbin

  obtain ⟨b, hb0, hb1⟩ : ∃ b : F, b ≠ 0 ∧ b ≠ 1 := by
    classical
    by_contra h
    push Not at h
    apply hF
    have h1 : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
      by_cases hx : x = 0
      · simp [hx]
      · simp [h x hx]
    have h2 := Finset.card_le_card h1
    have h3 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    have h4 := Fintype.one_lt_card (α := F)
    rw [Finset.card_univ] at h2
    omega
  have hω1 : ω ≠ 1 := by
    intro h
    have e := hω b
    have e1 := MulChar.one_apply_coe (R' := O) (Units.mk0 b hb0)
    rw [Units.val_mk0] at e1
    rw [h, e1, map_one] at e
    exact hb1 (ι.injective (e.symm.trans ι.map_one.symm))
  have hsum0 : ∑ a : F, ω⁻¹ a = 0 := MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hω1)
  set t : F → ℕ := fun a => (Algebra.trace (ZMod p) F a).val with ht
  refine ⟨1 + ∑ a : F, ω⁻¹ a * (t a : O) + c * ∑ a : F, ω⁻¹ a * r (t a), ?_, ?_⟩
  · refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hc)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_one, map_sum]
    have e : ∀ a : F, Ideal.Quotient.mk m (ω⁻¹ a * (t a : O)) =
        ι (a⁻¹ * algebraMap (ZMod p) F (Algebra.trace (ZMod p) F a)) := by
      intro a
      rw [map_mul, map_mul, MulChar.inv_apply', hω, map_natCast, ← map_natCast ι, ht,
        ZMod.natCast_val]
      rfl
    simp_rw [e]
    rw [← map_sum, sum_inv_mul_trace p F, map_neg, map_one, add_neg_cancel]
  · calc ∑ a : F, ω⁻¹ a * (1 + c) ^ t a
        = ∑ a : F, (ω⁻¹ a + c * (ω⁻¹ a * (t a : O) + c * (ω⁻¹ a * r (t a)))) :=
          Finset.sum_congr rfl fun a _ => by rw [hr]; ring
      _ = ∑ a : F, ω⁻¹ a + c * (∑ a : F, ω⁻¹ a * (t a : O) + c * ∑ a : F, ω⁻¹ a * r (t a)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = _ := by rw [hsum0]; ring

end ReciprocityTheory.PGsh

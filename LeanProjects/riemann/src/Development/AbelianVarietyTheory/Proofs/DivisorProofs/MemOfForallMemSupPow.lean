import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open IsLocalRing

namespace GlobalTheory.Poinc

open IsLocalRing in
variable {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] in
private theorem mem_of_forall_mem_sup_maximalIdeal_pow' (N : Ideal V) (x : V)
    (hx : ∀ e : ℕ, x ∈ N ⊔ maximalIdeal V ^ e) : x ∈ N := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := V) (M := V ⧸ N) (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hmem : Ideal.Quotient.mk N x ∈
      ⨅ i : ℕ, (maximalIdeal V ^ i • ⊤ : Submodule V (V ⧸ N)) := by
    refine Submodule.mem_iInf _ |>.2 fun e => ?_
    obtain ⟨a, ha, y, hy, rfl⟩ := Submodule.mem_sup.1 (hx e)
    have h1 : Ideal.Quotient.mk N (a + y) = y • Ideal.Quotient.mk N 1 := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, Algebra.smul_def, map_one,
        mul_one]
      rfl
    rw [h1]
    exact Submodule.smul_mem_smul hy Submodule.mem_top
  rw [hbot] at hmem
  exact hmem

open IsLocalRing in
variable {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] in
private theorem exists_not_mem_span_mul_maximalIdeal_sup_pow [IsDomain V] {g : V} (hg : g ≠ 0) :
    ∃ e : ℕ, g ∉ Ideal.span {g} * maximalIdeal V ⊔ maximalIdeal V ^ e := by
  by_contra h
  push_neg at h
  have hg' := mem_of_forall_mem_sup_maximalIdeal_pow' _ g h
  obtain ⟨z, hz, hgz⟩ := Ideal.mem_span_singleton_mul.1 hg'
  have hz1 : z = 1 := by
    have : g * (z - 1) = 0 := by rw [mul_sub, hgz, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hg
    · exact sub_eq_zero.1 h0
  exact (maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 (hz1 ▸ hz))

open IsLocalRing in

theorem _root_.GlobalTheory.Poinc.const_mod_prime_of_approx (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] [IsNoetherianRing V] (p : Ideal V) [p.IsPrime] (O' : Subring V)
    (hO : ∀ h ∈ O', h ∈ maximalIdeal V → h ∈ p) (g b u : V) (I : Ideal V) (hg : g ≠ 0)
    (hI : I ≤ maximalIdeal V)
    (H : ∀ e : ℕ, ∃ h ∈ O',
      h * g - u * (b * g) ∈ Ideal.span {b * g} * I ⊔ maximalIdeal V ^ e) :
    (IsUnit u → b ∈ maximalIdeal V → b ∈ p) ∧ (I ≤ p → ∃ h ∈ O', h - u * b ∈ p) := by
  obtain ⟨e₀, he₀⟩ := exists_not_mem_span_mul_maximalIdeal_sup_pow hg
  choose a haO haH using H
  have hspan : Ideal.span {b * g} ≤ Ideal.span {g} :=
    Ideal.span_singleton_le_span_singleton.2 ⟨b, mul_comm b g⟩
  have hbgI : Ideal.span {b * g} * I ≤ Ideal.span {g} * maximalIdeal V := Ideal.mul_mono hspan hI
  have hpow : ∀ {e : ℕ}, e₀ ≤ e → maximalIdeal V ^ e ≤ maximalIdeal V ^ e₀ :=
    fun h => Ideal.pow_le_pow_right h

  have hunit : ∀ x ∈ O', x * g ∈ Ideal.span {g} * maximalIdeal V ⊔ maximalIdeal V ^ e₀ →
      x ∈ p := by
    intro x hxO hx
    by_contra hxp
    have hxu : IsUnit x := by
      by_contra hnu
      exact hxp (hO x hxO ((mem_maximalIdeal x).2 hnu))
    apply he₀
    have key : ((hxu.unit⁻¹ : Vˣ) : V) * (x * g) = g := by
      rw [← mul_assoc, hxu.val_inv_mul, one_mul]
    have hmul := Ideal.mul_mem_left _ ((hxu.unit⁻¹ : Vˣ) : V) hx
    rwa [key] at hmul
  refine ⟨fun hu hb => ?_, fun hIp => ?_⟩
  · have hap : ∀ e, e₀ ≤ e → a e ∈ p := by
      intro e he
      refine hunit (a e) (haO e) ?_
      have h1 : a e * g = (a e * g - u * (b * g)) + g * (u * b) := by ring
      rw [h1]
      refine Ideal.add_mem _ ?_ (Ideal.mem_sup_left (Ideal.mem_span_singleton_mul.2
        ⟨u * b, Ideal.mul_mem_left _ _ hb, rfl⟩))
      exact sup_le_sup hbgI (hpow he) (haH e)
    have hN : u * (b * g) ∈ Ideal.span {g} * p ⊔ Ideal.span {b * g} * maximalIdeal V := by
      refine mem_of_forall_mem_sup_maximalIdeal_pow' _ _ fun e => ?_
      have h1 : u * (b * g) = g * a (max e e₀) - (a (max e e₀) * g - u * (b * g)) := by ring
      rw [h1]
      refine Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_sup_left
        (Ideal.mem_span_singleton_mul.2 ⟨_, hap _ (le_max_right _ _), rfl⟩))) ?_
      refine sup_le_sup (le_sup_of_le_right (Ideal.mul_mono_right hI))
        (Ideal.pow_le_pow_right (le_max_left e e₀)) (haH (max e e₀))
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hN
    obtain ⟨q, hq, rfl⟩ := Ideal.mem_span_singleton_mul.1 hy
    obtain ⟨r, hr, rfl⟩ := Ideal.mem_span_singleton_mul.1 hz
    have hcancel : b * (u - r) = q := by
      apply mul_left_cancel₀ hg
      linear_combination hyz.symm
    have hur : IsUnit (u - r) := by
      by_contra hnu
      have hm : u - r ∈ maximalIdeal V := (mem_maximalIdeal _).2 hnu
      have : u ∈ maximalIdeal V := by
        simpa using Ideal.add_mem _ hm hr
      exact (mem_maximalIdeal u).1 this hu
    rcases (inferInstance : p.IsPrime).mem_or_mem (hcancel ▸ hq) with h | h
    · exact h
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ h hur) (inferInstance : p.IsPrime).ne_top
  · have hdiff : ∀ e, e₀ ≤ e → a e - a e₀ ∈ p := by
      intro e he
      refine hunit _ (Subring.sub_mem _ (haO e) (haO e₀)) ?_
      have h1 : (a e - a e₀) * g =
          (a e * g - u * (b * g)) - (a e₀ * g - u * (b * g)) := by ring
      rw [h1]
      exact Ideal.sub_mem _ (sup_le_sup hbgI (hpow he) (haH e)) (sup_le_sup hbgI le_rfl (haH e₀))
    refine ⟨a e₀, haO e₀, ?_⟩
    have hN : (a e₀ - u * b) * g ∈ Ideal.span {g} * p := by
      refine mem_of_forall_mem_sup_maximalIdeal_pow' _ _ fun e => ?_
      have h1 : (a e₀ - u * b) * g =
          g * (-(a (max e e₀) - a e₀)) + (a (max e e₀) * g - u * (b * g)) := by ring
      rw [h1]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_mul.2
        ⟨_, neg_mem (hdiff _ (le_max_right _ _)), rfl⟩)) ?_
      exact sup_le_sup (Ideal.mul_mono hspan hIp) (Ideal.pow_le_pow_right (le_max_left e e₀))
        (haH (max e e₀))
    obtain ⟨q, hq, hgq⟩ := Ideal.mem_span_singleton_mul.1 hN
    have : a e₀ - u * b = q := by
      apply mul_left_cancel₀ hg
      rw [hgq, mul_comm]
    exact this ▸ hq

end GlobalTheory.Poinc

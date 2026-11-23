import Mathlib

universe u

open PowerSeries IsLocalRing

noncomputable section

namespace ReciprocityTheory.P1

section Complete

variable {A : Type*} [CommRing A] (I : Ideal A)

theorem map_C_sup_span_X :
    I.map (C : A →+* A⟦X⟧) ⊔ Ideal.span {X} = I.comap (constantCoeff (R := A)) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using ha
    · simp [Ideal.span_singleton_le_iff_mem]
  · intro f hf
    rw [f.eq_X_mul_shift_add_const]
    exact add_mem
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))

theorem mem_pow_comap_constantCoeff_iff (n : ℕ) (f : A⟦X⟧) :
    f ∈ I.comap (constantCoeff (R := A)) ^ n ↔ ∀ i, coeff i f ∈ I ^ (n - i) := by
  constructor
  · induction n generalizing f with
    | zero => simp
    | succ n ih =>
      intro hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf (fun a ha b hb i => ?_) (fun a b ha hb i => ?_)
      · rw [coeff_mul]
        refine sum_mem fun x hx => ?_
        have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
        have h1 := ih a ha x.1
        have h2 : coeff x.2 b ∈ I ^ (1 - x.2) := by
          rcases Nat.eq_zero_or_pos x.2 with h | h
          · rw [h]; simpa using hb
          · rw [show 1 - x.2 = 0 by omega]; simp
        have h3 := Ideal.mul_mem_mul h1 h2
        rw [← pow_add] at h3
        exact Ideal.pow_le_pow_right (by omega) h3
      · rw [map_add]; exact add_mem (ha i) (hb i)
  · intro h
    have hX : (X : A⟦X⟧) ∈ I.comap (constantCoeff (R := A)) := by simp
    rw [f.eq_X_pow_mul_shift_add_trunc n]
    refine add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hX n)) ?_
    rw [trunc_apply, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine sum_mem fun i hi => ?_
    have hi' : i < n := (Finset.mem_Ico.1 hi).2
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial,
      monomial_eq_C_mul_X_pow]
    have h1 : C (coeff i f) ∈ I.comap (constantCoeff (R := A)) ^ (n - i) := by
      have := Ideal.mem_map_of_mem (C : A →+* A⟦X⟧) (h i)
      rw [Ideal.map_pow] at this
      refine Ideal.pow_right_mono ?_ _ this
      rw [← map_C_sup_span_X]; exact le_sup_left
    have h2 := Ideal.mul_mem_mul h1 (Ideal.pow_mem_pow hX i)
    rwa [← pow_add, Nat.sub_add_cancel hi'.le] at h2

theorem isHausdorff_comap_constantCoeff [IsHausdorff I A] :
    IsHausdorff (I.comap (constantCoeff (R := A))) A⟦X⟧ where
  haus' f hf := by
    ext i
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hf (n + i)
    rw [SModEq.zero] at this ⊢
    simp only [smul_eq_mul, Ideal.mul_top] at this ⊢
    simpa using (mem_pow_comap_constantCoeff_iff I _ f).1 this i

theorem isPrecomplete_comap_constantCoeff [IsPrecomplete I A] :
    IsPrecomplete (I.comap (constantCoeff (R := A))) A⟦X⟧ where
  prec' F hF := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_pow_comap_constantCoeff_iff] at hF ⊢
    have : ∀ i, ∃ L : A, ∀ n, coeff i (F (n + i)) - L ∈ I ^ n := by
      intro i
      have := IsPrecomplete.prec' (I := I) (fun n => coeff i (F (n + i))) (by
        intro m n h
        simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using hF (show m + i ≤ n + i by omega) i)
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using this
    choose L hL using this
    refine ⟨mk L, fun n i => ?_⟩
    rcases le_or_gt i n with h | h
    · have := hL i (n - i)
      rw [Nat.sub_add_cancel h] at this
      simpa using this
    · rw [show n - i = 0 by omega]; simp

theorem isAdicComplete_comap_constantCoeff [IsAdicComplete I A] :
    IsAdicComplete (I.comap (constantCoeff (R := A))) A⟦X⟧ :=
  { isHausdorff_comap_constantCoeff I, isPrecomplete_comap_constantCoeff I with }

end Complete

theorem isAdicComplete_ps {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal R⟦X⟧) R⟦X⟧ := by
  have h : maximalIdeal R⟦X⟧ = (maximalIdeal R).comap (constantCoeff (R := R)) := by
    ext f
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      isUnit_iff_constantCoeff]
  rw [h]
  exact isAdicComplete_comap_constantCoeff _

end ReciprocityTheory.P1

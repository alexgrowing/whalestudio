import Formalism.HyperbolicPlaceProducts.DetIndexProductHyperbolicInequality

open NumberField

namespace Formalism.SLP.GlobalBoundRefinements.P

theorem eq_one_of_sub_one_mem_prime : Formalism.SLP.GlobalBoundRefinements.RootUnityTriv := by
  intro E _ _ α P hP hw h1 hm

  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ
    (NumberField.RingOfIntegers.isIntegral_coe α) (fun φ => by
      have := hw (NumberField.InfinitePlace.mk φ)
      rwa [NumberField.InfinitePlace.apply] at this)
  have hpowO : α ^ n = 1 := NumberField.RingOfIntegers.ext (by simpa using hpow)
  have hu : Units.ofPowEqOne α n hpowO hn.ne' ∈ NumberField.Units.torsion E := by
    rw [NumberField.Units.mem_torsion]
    intro w
    simpa using hw w
  have hm1 : α ^ Nat.card (NumberField.Units.torsion E) = 1 := by
    have := congrArg (fun g : NumberField.Units.torsion E => (((g : (RingOfIntegers E)ˣ)) : RingOfIntegers E))
      (pow_card_eq_one' (x := (⟨_, hu⟩ : NumberField.Units.torsion E)))
    simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Units.val_ofPowEqOne,
      OneMemClass.coe_one, Units.val_one] at this
    exact this
  by_contra hne
  apply hm

  have hsum : ∑ i ∈ Finset.range (Nat.card (NumberField.Units.torsion E)), α ^ i = 0 := by
    have h := geom_sum_mul α (Nat.card (NumberField.Units.torsion E))
    rw [hm1, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have hdiff : ∑ i ∈ Finset.range (Nat.card (NumberField.Units.torsion E)), (α ^ i - 1) ∈ P := by
    refine Ideal.sum_mem _ (fun i _ => ?_)
    obtain ⟨c, hc⟩ : α - 1 ∣ α ^ i - 1 := by simpa using sub_dvd_pow_sub_pow α 1 i
    rw [hc]
    exact P.mul_mem_right c h1
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    zero_sub, neg_mem_iff] at hdiff
  exact hdiff

theorem prod_infinitePlace_le_of_integral : Formalism.SLP.GlobalBoundRefinements.ThmBNorm := by
  intro F _ _ s q x hs hq hβ hw
  obtain ⟨β, hβ⟩ := hβ
  have hβ0 : β ≠ 0 := by
    intro h0
    have : s / q = 0 := by rw [← hβ, h0]; simp
    exact div_ne_zero hs hq this

  have hN : (1 : ℝ) ≤ ∏ w : NumberField.InfinitePlace F, w (s / q) ^ w.mult := by
    rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← hβ, ← Algebra.coe_norm_int]
    have hne : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ0
    have : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs hne
    exact_mod_cast this
  have hdiv : ∏ w : NumberField.InfinitePlace F, w (s / q) ^ w.mult =
      (∏ w : NumberField.InfinitePlace F, w s ^ w.mult) / ∏ w : NumberField.InfinitePlace F, w q ^ w.mult := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun w _ => ?_)
    rw [map_div₀, div_pow]
  have hqpos : 0 < ∏ w : NumberField.InfinitePlace F, w q ^ w.mult :=
    Finset.prod_pos (fun w _ => pow_pos (NumberField.InfinitePlace.pos_iff.mpr hq) _)
  have hsle : ∏ w : NumberField.InfinitePlace F, w s ^ w.mult ≤ ∏ w, (x w ^ 2) ^ w.mult :=
    Finset.prod_le_prod (fun w _ => pow_nonneg (NumberField.InfinitePlace.pos_iff.mpr hs).le _)
      (fun w _ => pow_le_pow_left₀ (NumberField.InfinitePlace.pos_iff.mpr hs).le (hw w) _)
  rw [hdiv, le_div_iff₀ hqpos, one_mul] at hN
  linarith

end Formalism.SLP.GlobalBoundRefinements.P

import Mathlib

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Formalism.L2.S.Pv.PsiTrCore

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k :=
  valuedAdicCompletion_eq_valuation' v k

theorem valued_algebraMap_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (r : F)) = v.intValuation r := by
  rw [valued_algebraMap]
  exact valuation_of_algebraMap v r

private theorem exists_integer_approx_valuation (v : HeightOneSpectrum (𝓞 F)) (k : F) (hk : v.valuation F k ≤ 1)
    (N : ℕ) : ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) ≤ WithZero.exp (-(N : ℤ)) := by
  classical
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 F) k
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hY : algebraMap (𝓞 F) F y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  set m := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {y})).factors with hm
  have hvy : v.intValuation y = WithZero.exp (-(m : ℤ)) := v.intValuation_if_neg hy0
  have hX : v.intValuation x =
      v.valuation F (algebraMap (𝓞 F) F x / algebraMap (𝓞 F) F y) * v.intValuation y := by
    rw [← valuation_of_algebraMap (K := F) v x, ← valuation_of_algebraMap (K := F) v y, ← map_mul,
      div_mul_cancel₀ _ hY]
  have hxm : x ∈ v.asIdeal ^ m := by
    rw [← intValuation_le_pow_iff_mem, hX, ← hvy]
    exact mul_le_of_le_one_left' hk
  have hdvd : v.asIdeal ^ m ∣ Ideal.span {y} := (intValuation_le_pow_iff_dvd v y m).mp hvy.le
  obtain ⟨J, hJ⟩ := hdvd
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hJv
    have hy1 : y ∈ v.asIdeal ^ m * J := hJ ▸ Ideal.mem_span_singleton_self y
    have hy2 : y ∈ v.asIdeal ^ (m + 1) := by
      rw [pow_succ]; exact Ideal.mul_mono_right hJv hy1
    have := (intValuation_le_pow_iff_mem v y (m + 1)).mpr hy2
    rw [hvy, WithZero.exp_le_exp] at this
    omega
  obtain ⟨t, htJ, htv⟩ := SetLike.not_le_iff_exists.mp hJv
  have hxt : x * t ∈ Ideal.span {y} := hJ ▸ Ideal.mul_mem_mul hxm htJ
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hxt
  obtain ⟨s, i, hi, hsi⟩ := v.isMaximal.exists_inv htv
  have htt : t * (s * ∑ j ∈ Finset.range N, i ^ j) = 1 - i ^ N := by
    have h1 : s * t = 1 - i := by linear_combination hsi
    calc t * (s * ∑ j ∈ Finset.range N, i ^ j) = (s * t) * ∑ j ∈ Finset.range N, i ^ j := by ring
      _ = 1 - i ^ N := by rw [h1, mul_neg_geom_sum]
  refine ⟨z * (s * ∑ j ∈ Finset.range N, i ^ j), ?_⟩
  set X := algebraMap (𝓞 F) F x
  set Y := algebraMap (𝓞 F) F y
  have hzF : algebraMap (𝓞 F) F z * Y = X * algebraMap (𝓞 F) F t := by
    simp only [X, Y, ← map_mul, hz]
  have httF : algebraMap (𝓞 F) F t * algebraMap (𝓞 F) F (s * ∑ j ∈ Finset.range N, i ^ j) =
      1 - algebraMap (𝓞 F) F (i ^ N) := by
    rw [← map_mul, htt, map_sub, map_one]
  have hZ : algebraMap (𝓞 F) F z = X * algebraMap (𝓞 F) F t / Y := eq_div_of_mul_eq hY hzF
  have key : X / Y - algebraMap (𝓞 F) F (z * (s * ∑ j ∈ Finset.range N, i ^ j)) =
      X / Y * algebraMap (𝓞 F) F (i ^ N) := by
    rw [map_mul, hZ]
    linear_combination (-(X / Y)) * httF
  rw [key, map_mul, valuation_of_algebraMap]
  have hIN : v.intValuation (i ^ N) ≤ WithZero.exp (-(N : ℤ)) :=
    (intValuation_le_pow_iff_mem v _ N).mpr (Ideal.pow_mem_pow hi N)
  exact (mul_le_of_le_one_left' hk).trans hIN

theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (a w : v.adicCompletion F)
    (ha : Valued.v a ≤ 1) (hw : w ≠ 0) (hw1 : Valued.v w ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (a - algebraMap F (v.adicCompletion F) (r : F)) < Valued.v w := by
  have hw0 : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).mpr hw
  obtain ⟨N, hN⟩ : ∃ N : ℕ, WithZero.exp (-(N : ℤ)) < Valued.v w := by
    refine ⟨(-(Valued.v w).log).toNat + 1, ?_⟩
    conv_rhs => rw [← WithZero.exp_log hw0]
    rw [WithZero.exp_lt_exp]
    omega
  have hU : IsOpen {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} := by
    have h := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict w)).preimage
      (continuous_id.sub continuous_const : Continuous fun y : v.adicCompletion F ↦ y - a)
    have e : {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} =
        (fun y : v.adicCompletion F ↦ y - a) ⁻¹'
          {x | Valued.v.restrict x < Valued.v.restrict w} := by
      ext y
      exact (Valuation.restrict_lt_iff (R := v.adicCompletion F) Valued.v).symm
    rw [e]
    exact h
  have hs : {y : v.adicCompletion F | Valued.v (y - a) < Valued.v w} ∈ nhds a := by
    refine hU.mem_nhds ?_
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact zero_lt_iff.mpr hw0
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F v).mem_nhds hs
  simp only [Set.mem_setOf_eq] at hk
  have hak : Valued.v (a - algebraMap F (v.adicCompletion F) k) < Valued.v w := by
    rwa [Valuation.map_sub_swap]
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← valued_algebraMap]
    have e : algebraMap F (v.adicCompletion F) k = a - (a - algebraMap F (v.adicCompletion F) k) := by
      ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le ha (hak.le.trans hw1))
  obtain ⟨r, hr⟩ := exists_integer_approx_valuation v k hk1 N
  refine ⟨r, ?_⟩
  have e : a - algebraMap F (v.adicCompletion F) (r : F) =
      (a - algebraMap F (v.adicCompletion F) k) +
        algebraMap F (v.adicCompletion F) (k - algebraMap (𝓞 F) F r) := by
    have hr' : (r : F) = algebraMap (𝓞 F) F r := rfl
    rw [map_sub, ← hr']
    ring
  rw [e]
  refine Valuation.map_add_lt _ hak ?_
  rw [valued_algebraMap]
  exact lt_of_le_of_lt hr hN

theorem exists_approx (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F)
    (n : 𝓞 F) (hn : n ≠ 0) :
    ∃ b : 𝓞 F, ∀ v, Valued.v (a v - algebraMap F (v.adicCompletion F) (b : F)) ≤ v.intValuation n := by
  classical
  have hspan : Ideal.span {n} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hn
  set T := (Ideal.finite_factors hspan).toFinset with hT
  have hmemT : ∀ v, v ∈ T ↔ n ∈ v.asIdeal := fun v ↦ by
    simp [T, Set.Finite.mem_toFinset, Ideal.dvd_span_singleton]
  have hw : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (n : F) ≠ 0 := by
    intro v h
    have := valued_algebraMap_int v n
    rw [h, map_zero, intValuation_if_neg v hn] at this
    exact WithZero.exp_ne_zero this.symm
  have hr : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      Valued.v (a v - algebraMap F (v.adicCompletion F) (r : F)) <
        Valued.v (algebraMap F (v.adicCompletion F) (n : F)) := fun v ↦
    exists_int_near v (a v) _ ((mem_adicCompletionIntegers (𝓞 F) F v).mp (ha v)) (hw v)
      (by rw [valued_algebraMap_int]; exact intValuation_le_one v n)
  choose r hr using hr
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum (𝓞 F) ↦ v.asIdeal)
    (fun v ↦ (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n})).factors)
    (fun v _ ↦ v.prime) (fun i _ j _ hij h ↦ hij (HeightOneSpectrum.ext h)) (fun i ↦ r i.1)
  refine ⟨b, fun v ↦ ?_⟩
  have hb1 : Valued.v (algebraMap F (v.adicCompletion F) (b : F)) ≤ 1 := by
    rw [valued_algebraMap_int]; exact intValuation_le_one v b
  by_cases hv : v ∈ T
  · have h1 := (hr v).le
    rw [valued_algebraMap_int] at h1
    have h2 : Valued.v (algebraMap F (v.adicCompletion F) (r v : F) -
        algebraMap F (v.adicCompletion F) (b : F)) ≤ v.intValuation n := by
      rw [← map_sub, show (r v : F) - (b : F) = ((r v - b : 𝓞 F) : F) from
        (map_sub (algebraMap (𝓞 F) F) _ _).symm, valued_algebraMap_int, ← Valuation.map_neg,
        neg_sub, intValuation_if_neg v hn]
      exact (intValuation_le_pow_iff_mem v _ _).mpr (hb v hv)
    have e : a v - algebraMap F (v.adicCompletion F) (b : F) =
        (a v - algebraMap F (v.adicCompletion F) (r v : F)) +
          (algebraMap F (v.adicCompletion F) (r v : F) - algebraMap F (v.adicCompletion F) (b : F)) := by
      ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le h1 h2)
  · have hn1 : v.intValuation n = 1 := le_antisymm (intValuation_le_one v n)
      (not_lt.mp fun h ↦ hv ((hmemT v).mpr ((intValuation_lt_one_iff_mem v n).mp h)))
    rw [hn1]
    exact (Valuation.map_sub _ _ _).trans
      (max_le ((mem_adicCompletionIntegers (𝓞 F) F v).mp (ha v)) hb1)

theorem exists_decomp (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F)
    (n : 𝓞 F) (hn : n ≠ 0) :
    ∃ b : 𝓞 F, ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧
      a = algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F) +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (n : F) * c := by
  obtain ⟨b, hb⟩ := exists_approx a ha n hn
  have hnF : (n : F) ≠ 0 := by
    have := (IsFractionRing.injective (𝓞 F) F).ne hn
    rwa [map_zero] at this
  have hA : ∀ (k : F) (v : HeightOneSpectrum (𝓞 F)),
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = algebraMap F (v.adicCompletion F) k :=
    fun k v ↦ rfl
  refine ⟨b, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((n : F)⁻¹) *
    (a - algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F)), fun v ↦ ?_, ?_⟩
  · rw [mem_adicCompletionIntegers]
    change Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) ((n : F)⁻¹)) v *
      (a v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F)) v)) ≤ 1
    rw [hA, hA, map_mul, map_inv₀, map_inv₀, valued_algebraMap_int]
    have hne : v.intValuation n ≠ 0 := by
      rw [intValuation_if_neg v hn]; exact WithZero.exp_ne_zero
    calc (v.intValuation n)⁻¹ * Valued.v (a v - algebraMap F (v.adicCompletion F) (b : F))
        ≤ (v.intValuation n)⁻¹ * v.intValuation n := by
          have hbv := hb v
          gcongr
      _ = 1 := inv_mul_cancel₀ hne
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hnF, map_one, one_mul]
    ring

end Formalism.L2.S.Pv.PsiTrCore

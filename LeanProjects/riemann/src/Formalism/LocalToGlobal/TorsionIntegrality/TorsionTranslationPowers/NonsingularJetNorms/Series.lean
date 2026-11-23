import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementU

open PowerSeries Finset

noncomputable section

namespace Formalism.L2.Th1.E

namespace Ser

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_sum_le_one {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

theorem norm_sum_lt_one {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, ‖f i‖ < 1) :
    ‖∑ i ∈ s, f i‖ < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact h a (Finset.mem_insert_self a s)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem norm_mul_le_one {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

theorem intS_C {a : K} (ha : ‖a‖ ≤ 1) : IntS (C a) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · simp

theorem intS_one : IntS (1 : K⟦X⟧) := by
  have := intS_C (K := K) (a := 1) (by simp)
  simpa using this

theorem intS_X : IntS (X : K⟦X⟧) := by
  intro n
  rw [coeff_X]
  split_ifs <;> simp

theorem intS_add {f g : K⟦X⟧} (hf : IntS f) (hg : IntS g) : IntS (f + g) := by
  intro n
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem intS_neg {f : K⟦X⟧} (hf : IntS f) : IntS (-f) := by
  intro n
  rw [map_neg, norm_neg]
  exact hf n

theorem intS_sub {f g : K⟦X⟧} (hf : IntS f) (hg : IntS g) : IntS (f - g) := by
  rw [sub_eq_add_neg]
  exact intS_add hf (intS_neg hg)

theorem intS_mul {f g : K⟦X⟧} (hf : IntS f) (hg : IntS g) : IntS (f * g) := by
  intro n
  rw [coeff_mul]
  exact norm_sum_le_one _ _ (fun p _ => norm_mul_le_one (hf _) (hg _))

theorem intS_pow {f : K⟦X⟧} (hf : IntS f) (n : ℕ) : IntS (f ^ n) := by
  induction n with
  | zero => simpa using intS_one (K := K)
  | succ n ih => rw [pow_succ]; exact intS_mul ih hf

theorem oneUnit_mul {f g : K⟦X⟧} (hf : OneUnit f) (hg : OneUnit g) : OneUnit (f * g) :=
  ⟨by rw [map_mul, hf.1, hg.1, one_mul], intS_mul hf.2 hg.2⟩

theorem oneUnit_pow {f : K⟦X⟧} (hf : OneUnit f) (n : ℕ) : OneUnit (f ^ n) :=
  ⟨by rw [map_pow, hf.1, one_pow], intS_pow hf.2 n⟩

theorem oneUnit_of_mul_eq_one {f g : K⟦X⟧} (hf : OneUnit f) (h : f * g = 1) : OneUnit g := by
  have h0 : constantCoeff g = 1 := by
    have := congrArg (constantCoeff (R := K)) h
    rwa [map_mul, hf.1, one_mul, map_one] at this
  refine ⟨h0, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_zero_eq_constantCoeff_apply, h0]; simp
    · have h1 : coeff n (f * g) = 0 := by
        rw [h, coeff_one, if_neg hn.ne']
      rw [coeff_mul, ← Finset.add_sum_erase _ _ (show (0, n) ∈ antidiagonal n by simp)] at h1
      simp only [coeff_zero_eq_constantCoeff_apply, hf.1, one_mul] at h1
      rw [eq_neg_of_add_eq_zero_left h1, norm_neg]
      refine norm_sum_le_one _ _ (fun p hp => norm_mul_le_one (hf.2 _) (ih _ ?_))
      rw [Finset.mem_erase, HasAntidiagonal.mem_antidiagonal] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have : p.1 ≠ 0 := by
        intro h3
        apply hp1
        ext
        · exact h3
        · simp only; omega
      omega

theorem intS_iff_integral (f : K⟦X⟧) : IntS f ↔ Formalism.DworkPowerSeriesWeights.Integral (ι := Unit) f := by
  constructor
  · intro h n
    have := h (n ())
    rwa [coeff_def (s := n) rfl] at this
  · intro h n
    exact h (Finsupp.single () n)

theorem unitAt_mul {j k : ℕ} {f g : K⟦X⟧} (hf : UnitAt j f) (hg : UnitAt k g) :
    UnitAt (j + k) (f * g) := by
  obtain ⟨a, V, ha, hV, rfl⟩ := hf
  obtain ⟨b, W, hb, hW, rfl⟩ := hg
  refine ⟨a * b, V * W, by rw [norm_mul, ha, hb, one_mul], oneUnit_mul hV hW, ?_⟩
  rw [map_mul, pow_add]
  ring

theorem unitAt_pow {k : ℕ} {f : K⟦X⟧} (hf : UnitAt k f) (n : ℕ) : UnitAt (k * n) (f ^ n) := by
  obtain ⟨a, V, ha, hV, rfl⟩ := hf
  refine ⟨a ^ n, V ^ n, by rw [norm_pow, ha, one_pow], oneUnit_pow hV n, ?_⟩
  rw [map_pow, pow_mul, mul_pow, mul_pow]

theorem unitAt_of_coeff {k : ℕ} {f : K⟦X⟧} (hf : IntS f) (h0 : ∀ i, i < k → coeff i f = 0)
    (hk : ‖coeff k f‖ = 1) : UnitAt k f := by
  obtain ⟨h, rfl⟩ := X_pow_dvd_iff.mpr h0
  have hc : ∀ d, coeff (d + k) (X ^ k * h) = coeff d h := fun d => coeff_X_pow_mul h k d
  have hk' : coeff k (X ^ k * h) = constantCoeff h := by
    have := hc 0
    rwa [zero_add, coeff_zero_eq_constantCoeff_apply] at this
  rw [hk'] at hk
  have hne : constantCoeff h ≠ 0 := by
    intro h3
    rw [h3, norm_zero] at hk
    exact zero_ne_one hk
  refine ⟨constantCoeff h, C (constantCoeff h)⁻¹ * h, hk, ⟨?_, ?_⟩, ?_⟩
  · rw [map_mul, constantCoeff_C, inv_mul_cancel₀ hne]
  · refine intS_mul (intS_C ?_) ?_
    · rw [norm_inv, hk, inv_one]
    · intro d
      rw [← hc d]
      exact hf _
  · have : C (constantCoeff h) * C (constantCoeff h)⁻¹ = (1 : K⟦X⟧) := by
      rw [← map_mul, mul_inv_cancel₀ hne, map_one]
    calc X ^ k * h = (C (constantCoeff h) * C (constantCoeff h)⁻¹) * (X ^ k * h) := by
          rw [this, one_mul]
      _ = _ := by ring

theorem unitAt_intS {k : ℕ} {f : K⟦X⟧} (hf : UnitAt k f) : IntS f := by
  obtain ⟨a, V, ha, hV, rfl⟩ := hf
  exact intS_mul (intS_mul (intS_C ha.le) (intS_pow intS_X k)) hV.2

theorem unitAt_gaussOne {k : ℕ} {f : K⟦X⟧} (hf : UnitAt k f) : GaussOne f := by
  refine ⟨unitAt_intS hf, k, ?_⟩
  obtain ⟨a, V, ha, hV, rfl⟩ := hf
  have : coeff (0 + k) (X ^ k * V) = coeff 0 V := coeff_X_pow_mul V k 0
  rw [mul_assoc, coeff_C_mul, norm_mul, ha, one_mul]
  rw [zero_add, coeff_zero_eq_constantCoeff_apply, hV.1] at this
  rw [this, norm_one]

theorem unitAt_C_mul {k : ℕ} {f : K⟦X⟧} {a : K} (ha : ‖a‖ = 1) (hf : UnitAt k f) :
    UnitAt k (C a * f) := by
  obtain ⟨b, V, hb, hV, rfl⟩ := hf
  refine ⟨a * b, V, by rw [norm_mul, ha, hb, one_mul], hV, ?_⟩
  rw [map_mul]
  ring

theorem rootInt {N : ℕ} {g : K⟦X⟧} (hN : ‖(N : K)‖ = 1) (h0 : constantCoeff g = 1)
    (hg : IntS (g ^ N)) : IntS g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_zero_eq_constantCoeff_apply, h0]; simp
    · set A : K⟦X⟧ := PowerSeries.mk (fun i => if i < n then coeff i g else 0) with hA
      have hAint : IntS A := by
        intro i
        rw [hA, coeff_mk]
        split_ifs with hi
        · exact ih i hi
        · simp
      have hA0 : constantCoeff A = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply, hA, coeff_mk, if_pos hn,
          coeff_zero_eq_constantCoeff_apply, h0]
      have hdvd : (X : K⟦X⟧) ^ n ∣ g - A := by
        rw [X_pow_dvd_iff]
        intro m hm
        rw [map_sub, hA, coeff_mk, if_pos hm, sub_self]
      obtain ⟨B, hB⟩ := hdvd
      have hB0 : constantCoeff B = coeff n g := by
        have h1 : coeff (0 + n) (X ^ n * B) = coeff 0 B := coeff_X_pow_mul B n 0
        rw [← hB, zero_add, map_sub, hA, coeff_mk, if_neg (lt_irrefl n), sub_zero,
          coeff_zero_eq_constantCoeff_apply] at h1
        exact h1.symm
      set S : K⟦X⟧ := ∑ i ∈ range N, g ^ i * A ^ (N - 1 - i) with hS
      have hS0 : constantCoeff S = (N : K) := by
        rw [hS, map_sum]
        simp [h0, hA0]
      have hfac : g ^ N - A ^ N = X ^ n * (B * S) := by
        rw [← (Commute.all g A).geom_sum₂_mul N, hB, ← hS]
        ring
      have h2 : coeff n (g ^ N - A ^ N) = coeff n g * (N : K) := by
        have h1 : coeff (0 + n) (X ^ n * (B * S)) = coeff 0 (B * S) := coeff_X_pow_mul _ n 0
        have h4 : constantCoeff (B * S) = coeff n g * (N : K) := by rw [map_mul, hB0, hS0]
        rw [zero_add, coeff_zero_eq_constantCoeff_apply, h4] at h1
        rw [hfac, h1]
      have h3 : ‖coeff n (g ^ N - A ^ N)‖ ≤ 1 := intS_sub hg (intS_pow hAint N) n
      rwa [h2, norm_mul, hN, mul_one] at h3

theorem gaussMul {f g : K⟦X⟧} (hf : GaussOne f) (hg : GaussOne g) : GaussOne (f * g) := by
  classical
  obtain ⟨hfi, hfe⟩ := hf
  obtain ⟨hgi, hge⟩ := hg
  refine ⟨intS_mul hfi hgi, Nat.find hfe + Nat.find hge, ?_⟩
  set i := Nat.find hfe with hi
  set j := Nat.find hge with hj
  have hi1 : ‖coeff i f‖ = 1 := Nat.find_spec hfe
  have hj1 : ‖coeff j g‖ = 1 := Nat.find_spec hge
  have hilt : ∀ m, m < i → ‖coeff m f‖ < 1 := fun m hm =>
    lt_of_le_of_ne (hfi m) (Nat.find_min hfe hm)
  have hjlt : ∀ m, m < j → ‖coeff m g‖ < 1 := fun m hm =>
    lt_of_le_of_ne (hgi m) (Nat.find_min hge hm)
  rw [coeff_mul, ← Finset.add_sum_erase _ _ (show (i, j) ∈ antidiagonal (i + j) by simp)]
  have hmain : ‖coeff i f * coeff j g‖ = 1 := by rw [norm_mul, hi1, hj1, one_mul]
  have hrest : ‖∑ p ∈ (antidiagonal (i + j)).erase (i, j), coeff p.1 f * coeff p.2 g‖ < 1 := by
    refine norm_sum_lt_one _ _ (fun p hp => ?_)
    rw [Finset.mem_erase, HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [norm_mul]
    have hcase : p.1 < i ∨ p.2 < j := by
      by_contra hcon
      push Not at hcon
      apply hp1
      ext
      · simp only; omega
      · simp only; omega
    rcases hcase with hc | hc
    · calc ‖coeff p.1 f‖ * ‖coeff p.2 g‖ ≤ ‖coeff p.1 f‖ * 1 :=
            mul_le_mul_of_nonneg_left (hgi _) (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact hilt _ hc
    · calc ‖coeff p.1 f‖ * ‖coeff p.2 g‖ ≤ 1 * ‖coeff p.2 g‖ :=
            mul_le_mul_of_nonneg_right (hfi _) (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hjlt _ hc
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hmain]; exact hrest.ne'), hmain]
  exact max_eq_left hrest.le

end Ser

theorem integrality_rules : IntRules := by
  intro K _ _
  exact ⟨fun _ ha => Ser.intS_C ha, Ser.intS_X, fun _ _ => Ser.intS_add, fun _ => Ser.intS_neg,
    fun _ _ => Ser.intS_mul, fun _ n hf => Ser.intS_pow hf n, fun _ _ => Ser.oneUnit_mul,
    fun _ n hf => Ser.oneUnit_pow hf n, fun _ _ => Ser.oneUnit_of_mul_eq_one,
    Ser.intS_iff_integral⟩

theorem unit_at_rules : UnitAtRules := by
  intro K _ _
  exact ⟨fun _ _ _ _ => Ser.unitAt_mul, fun _ n _ hf => Ser.unitAt_pow hf n,
    fun _ _ => Ser.unitAt_of_coeff, fun _ _ => Ser.unitAt_gaussOne,
    fun _ _ _ => Ser.unitAt_C_mul⟩

theorem root_integral_alt : RootInt := by
  intro K _ _ N g hN h0 hg
  exact Ser.rootInt hN h0 hg

theorem gauss_multiplicative : GaussMul := by
  intro K _ _ f g hf hg
  exact Ser.gaussMul hf hg

end Formalism.L2.Th1.E

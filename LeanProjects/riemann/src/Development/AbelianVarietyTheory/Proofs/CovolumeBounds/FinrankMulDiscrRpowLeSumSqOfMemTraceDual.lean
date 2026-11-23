import Mathlib

open NumberField Module
open scoped nonZeroDivisors

namespace GlobalTheory

theorem card_mul_rpow_prod_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * (∏ i, z i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, z i := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) z (fun _ _ => by positivity)
    (by simp [hc.ne']) (fun i _ => hz i)
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz i), ← Finset.mul_sum] at h
  calc _ ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, z i) := by gcongr
    _ = _ := by field_simp

section General

variable {K : Type*} [Field K] [NumberField K]

theorem norm_eq_prod_complexEmbeddings (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ x := by
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  simp

theorem trace_eq_sum_complexEmbeddings (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ x := by
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)]
  simp

theorem abs_norm_eq_prod_complexEmbeddings (x : K) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  rw [← norm_prod, ← norm_eq_prod_complexEmbeddings, Complex.norm_ratCast]

theorem finrank_mul_abs_norm_rpow_le_sum (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ ((finrank ℚ K : ℝ)⁻¹)
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ := by
  rw [abs_norm_eq_prod_complexEmbeddings, ← Embeddings.card K ℂ]
  exact card_mul_rpow_prod_le_sum _ fun _ => norm_nonneg _

theorem finrank_mul_abs_norm_rpow_le_sum_sq (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_abs_norm_rpow_le_sum (x ^ 2)
  simp only [map_pow, norm_pow, Rat.cast_pow, abs_pow] at h
  rwa [div_eq_mul_inv, Real.rpow_mul (abs_nonneg _), Real.rpow_two]

theorem one_le_abs_norm_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    1 ≤ |Algebra.norm ℚ x| := by
  have hn : IsIntegral ℤ (Algebra.norm ℚ x) := Algebra.isIntegral_norm ℚ hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hm
    exact h0 hm
  rw [← hm, eq_intCast]
  exact_mod_cast Int.one_le_abs hm0

theorem finrank_le_sum_norm_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) ≤ ∑ σ : K →+* ℂ, ‖σ x‖ := by
  refine le_trans ?_ (finrank_mul_abs_norm_rpow_le_sum x)
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    exact_mod_cast one_le_abs_norm_of_isIntegral hx h0
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow h1 (by positivity))

theorem eq_zero_of_isIntegral_of_sum_norm_lt {x : K} (hx : IsIntegral ℤ x)
    (h : ∑ σ : K →+* ℂ, ‖σ x‖ < finrank ℚ K) : x = 0 := by
  by_contra h0
  exact absurd h (not_lt.mpr (finrank_le_sum_norm_of_isIntegral hx h0))

theorem absNorm_le_abs_norm_of_mem {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) : FractionalIdeal.absNorm J ≤ |Algebra.norm ℚ x| := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact h0 ((FractionalIdeal.mem_zero_iff _).mp hx)
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J⁻¹ ≤ 1 := by
    calc _ ≤ J * J⁻¹ := by
          gcongr
          exact FractionalIdeal.spanSingleton_le_iff_mem.mpr hx
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hI' : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = I * J := by
    rw [hI, inv_mul_cancel_right₀ hJ]
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    exact h0 (FractionalIdeal.spanSingleton_eq_zero_iff.mp (by simpa using hI'))
  have h1 : (1 : ℚ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), hI', map_mul,
    FractionalIdeal.coeIdeal_absNorm]
  exact le_mul_of_one_le_left (FractionalIdeal.absNorm_nonneg _) h1

theorem finrank_mul_absNorm_rpow_le_sum_sq {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine le_trans ?_ (finrank_mul_abs_norm_rpow_le_sum_sq x)
  have h1 : ((FractionalIdeal.absNorm J : ℚ) : ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    exact_mod_cast absNorm_le_abs_norm_of_mem hx h0
  have h2 : (0 : ℝ) ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg J
  gcongr

variable (K) in

theorem dual_one_eq_inv_differentIdeal :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]

variable (K) in

theorem absNorm_inv_differentIdeal :
    FractionalIdeal.absNorm (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
      = |(discr K : ℚ)|⁻¹ := by
  rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal K]
  simp

theorem finrank_mul_discr_rpow_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_absNorm_rpow_le_sum_sq hx h0
  rw [absNorm_inv_differentIdeal] at h
  rw [neg_div, Real.rpow_neg (abs_nonneg _), ← Real.inv_rpow (abs_nonneg _)]
  simpa using h

theorem finrank_div_rootDiscr_sq_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) / rootDiscr K ^ 2 ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_discr_rpow_le_sum_sq hx h0
  rw [neg_div, Real.rpow_neg (abs_nonneg _), div_eq_inv_mul, Real.rpow_mul (abs_nonneg _),
    Real.rpow_two] at h
  rw [rootDiscr_def, div_eq_mul_inv]
  simpa using h

theorem finrank_mul_discr_rpow_le_sum_sq_of_mem_traceDual {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine finrank_mul_discr_rpow_le_sum_sq ?_ h0
  rw [← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  exact hx

omit [NumberField K] in

theorem eq_zero_of_embedding_eq_zero {A : Type*} [Ring A] [Nontrivial A] (σ : K →+* A) {x : K}
    (h : σ x = 0) : x = 0 :=
  (map_eq_zero σ).mp h

theorem exists_int_eq_mul_trace_of_mem_traceDual {q : ℚ} {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (Submodule.span (𝓞 K) {(q : K)})) :
    ∃ m : ℤ, q * Algebra.trace ℚ K x = m := by
  obtain ⟨m, hm⟩ := Submodule.mem_traceDual.mp hx q (Submodule.mem_span_singleton_self _)
  refine ⟨m, ?_⟩
  rw [Algebra.traceForm_apply, mul_comm, ← Rat.smul_def, map_smul, smul_eq_mul, eq_intCast] at hm
  exact hm.symm

theorem trace_mem_of_mem_traceDual {q : ℚ} (hq : q ≠ 0) {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (Submodule.span (𝓞 K) {(q : K)})) :
    ∃ m : ℤ, Algebra.trace ℚ K x = q⁻¹ * m := by
  obtain ⟨m, hm⟩ := exists_int_eq_mul_trace_of_mem_traceDual hx
  exact ⟨m, by rw [← hm, inv_mul_cancel_left₀ hq]⟩

theorem trace_mem_of_mem_dual_spanSingleton {q : ℚ} (hq : q ≠ 0) {x : K}
    (hx : x ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton (𝓞 K)⁰ (q : K))) :
    ∃ m : ℤ, Algebra.trace ℚ K x = q⁻¹ * m := by
  refine trace_mem_of_mem_traceDual hq ?_
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual ℤ ℚ
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (by exact_mod_cast hq)),
    FractionalIdeal.coe_spanSingleton] at hx
  exact hx

end General

section TotallyReal

variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]

omit [NumberField F] in
variable (F) in

theorem bijective_ofRealHom_comp :
    Function.Bijective (fun σ : F →+* ℝ => Complex.ofRealHom.comp σ) := by
  refine ⟨fun σ τ h => RingHom.ext fun x => ?_, fun φ => ?_⟩
  · simpa using RingHom.congr_fun h x
  · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x => by simp⟩

variable (F) in

theorem card_realEmbeddings : Fintype.card (F →+* ℝ) = finrank ℚ F := by
  rw [← Embeddings.card F ℂ]
  exact Fintype.card_of_bijective (bijective_ofRealHom_comp F)

theorem norm_eq_prod_realEmbeddings (x : F) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ σ : F →+* ℝ, σ x := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, norm_eq_prod_complexEmbeddings, Complex.ofReal_prod]
  exact ((bijective_ofRealHom_comp F).prod_comp (fun φ => φ x)).symm

theorem trace_eq_sum_realEmbeddings (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ σ : F →+* ℝ, σ x := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, trace_eq_sum_complexEmbeddings, Complex.ofReal_sum]
  exact ((bijective_ofRealHom_comp F).sum_comp (fun φ => φ x)).symm

theorem sum_abs_realEmbeddings (x : F) :
    ∑ σ : F →+* ℝ, |σ x| = ∑ σ : F →+* ℂ, ‖σ x‖ := by
  rw [← (bijective_ofRealHom_comp F).sum_comp (fun φ => ‖φ x‖)]
  simp

theorem norm_pos_of_totallyPos {a : F} (ha : ∀ σ : F →+* ℝ, 0 < σ a) : 0 < Algebra.norm ℚ a := by
  have : (0 : ℝ) < ((Algebra.norm ℚ a : ℚ) : ℝ) := by
    rw [norm_eq_prod_realEmbeddings]
    exact Finset.prod_pos fun σ _ => ha σ
  exact_mod_cast this

theorem ne_zero_of_totallyPos {a : F} (ha : ∀ σ : F →+* ℝ, 0 < σ a) : a ≠ 0 := by
  rintro rfl
  simpa using norm_pos_of_totallyPos ha

theorem finrank_mul_norm_rpow_le_trace {a : F} (ha : ∀ σ : F →+* ℝ, 0 < σ a) :
    (finrank ℚ F : ℝ) * ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (1 / (finrank ℚ F : ℝ))
      ≤ ((Algebra.trace ℚ F a : ℚ) : ℝ) := by
  have h := finrank_mul_abs_norm_rpow_le_sum a
  have hp : (0 : ℝ) < ((Algebra.norm ℚ a : ℚ) : ℝ) := by
    exact_mod_cast norm_pos_of_totallyPos ha
  rw [abs_of_pos hp, ← sum_abs_realEmbeddings,
    Finset.sum_congr rfl fun σ _ => abs_of_pos (ha σ)] at h
  rwa [one_div, trace_eq_sum_realEmbeddings]

theorem finrank_le_trace_of_isIntegral {a : F} (hi : IsIntegral ℤ a)
    (ha : ∀ σ : F →+* ℝ, 0 < σ a) : (finrank ℚ F : ℚ) ≤ Algebra.trace ℚ F a := by
  have h := finrank_le_sum_norm_of_isIntegral hi (ne_zero_of_totallyPos ha)
  rw [← sum_abs_realEmbeddings, Finset.sum_congr rfl fun σ _ => abs_of_pos (ha σ),
    ← trace_eq_sum_realEmbeddings] at h
  exact_mod_cast h

theorem eq_zero_of_isIntegral_of_sum_abs_lt {x : F} (hx : IsIntegral ℤ x)
    (h : ∑ σ : F →+* ℝ, |σ x| < finrank ℚ F) : x = 0 :=
  eq_zero_of_isIntegral_of_sum_norm_lt hx (by rwa [← sum_abs_realEmbeddings])

theorem eq_zero_or_totallyPos {a : F} (ha : ∀ σ : F →+* ℝ, 0 ≤ σ a) :
    a = 0 ∨ ∀ σ : F →+* ℝ, 0 < σ a := by
  by_cases h0 : a = 0
  · exact Or.inl h0
  · exact Or.inr fun σ => (ha σ).lt_of_ne' fun h => h0 (eq_zero_of_embedding_eq_zero σ h)

end TotallyReal

theorem trace_lower_bounds (F K : Type*) [Field F] [NumberField F] [IsTotallyReal F]
    [Field K] [NumberField K] :
    (∀ a : F, (∀ σ : F →+* ℝ, 0 < σ a) →
      (finrank ℚ F : ℝ) * ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (1 / (finrank ℚ F : ℝ))
        ≤ ((Algebra.trace ℚ F a : ℚ) : ℝ)) ∧
    (∀ a : F, IsIntegral ℤ a → (∀ σ : F →+* ℝ, 0 < σ a) →
      (finrank ℚ F : ℚ) ≤ Algebra.trace ℚ F a) ∧
    (∀ a : K, IsIntegral ℤ a → ∑ σ : K →+* ℂ, ‖σ a‖ < finrank ℚ K → a = 0) ∧
    (∀ x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹, x ≠ 0 →
      (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
        ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2) ∧
    (∀ (J : FractionalIdeal (𝓞 K)⁰ K), ∀ x ∈ J, x ≠ 0 →
      (finrank ℚ K : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ (2 / (finrank ℚ K : ℝ))
        ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2) ∧
    (∀ (a : F) (σ : F →+* ℝ), σ a = 0 → a = 0) ∧
    (∀ q : ℚ, q ≠ 0 → ∀ x ∈ Submodule.traceDual ℤ ℚ (Submodule.span (𝓞 F) {(q : F)}),
      ∃ m : ℤ, Algebra.trace ℚ F x = q⁻¹ * m) :=
  ⟨fun _ ha => finrank_mul_norm_rpow_le_trace ha,
    fun _ hi ha => finrank_le_trace_of_isIntegral hi ha,
    fun _ hi h => eq_zero_of_isIntegral_of_sum_norm_lt hi h,
    fun _ hx h0 => finrank_mul_discr_rpow_le_sum_sq hx h0,
    fun _ _ hx h0 => finrank_mul_absNorm_rpow_le_sum_sq hx h0,
    fun _ σ h => eq_zero_of_embedding_eq_zero σ h,
    fun _ hq _ hx => trace_mem_of_mem_traceDual hq hx⟩

end GlobalTheory

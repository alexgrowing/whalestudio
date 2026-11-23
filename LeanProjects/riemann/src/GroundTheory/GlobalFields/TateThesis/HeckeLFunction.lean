import Mathlib
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableAbsNormRpowInv

open Topology Filter NumberField IsDedekindDomain WithZero FractionalIdeal Function Ideal
open scoped NumberField.AdeleRing nonZeroDivisors

namespace GroundTheory.Global

noncomputable section

section Factored

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem heightOneSpectrum_eq_of_dvd {v w : HeightOneSpectrum R} (h : w.asIdeal ∣ v.asIdeal) :
    w = v :=
  HeightOneSpectrum.ext (associated_iff_eq.1
    ((HeightOneSpectrum.prime w).associated_of_dvd (HeightOneSpectrum.prime v) h))

theorem heightOneSpectrum_eq_of_dvd_pow {v w : HeightOneSpectrum R} {k : ℕ}
    (h : w.asIdeal ∣ v.asIdeal ^ k) : w = v :=
  heightOneSpectrum_eq_of_dvd ((HeightOneSpectrum.prime w).dvd_of_dvd_pow h)

theorem exists_heightOneSpectrum_dvd {I : Ideal R} (h0 : I ≠ ⊥) (h1 : I ≠ ⊤) :
    ∃ v : HeightOneSpectrum R, v.asIdeal ∣ I := by
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I h1
  have hM0 : M ≠ ⊥ := fun h ↦ h0 (le_bot_iff.1 (h ▸ hIM))
  exact ⟨⟨M, hM.isPrime, hM0⟩, Ideal.dvd_iff_le.2 hIM⟩

def factoredIdeals (S : Finset (HeightOneSpectrum R)) : Set (Ideal R) :=
  {I | I ≠ ⊥ ∧ ∀ v : HeightOneSpectrum R, v.asIdeal ∣ I → v ∈ S}

theorem factoredIdeals_empty : factoredIdeals (∅ : Finset (HeightOneSpectrum R)) = {⊤} := by
  ext I
  simp only [factoredIdeals, Set.mem_ofPred_eq, Finset.notMem_empty, imp_false,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, h⟩
    by_contra h1
    obtain ⟨v, hv⟩ := exists_heightOneSpectrum_dvd h0 h1
    exact h v hv
  · rintro rfl
    exact ⟨top_ne_bot, fun v hv ↦ v.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd hv))⟩

theorem pow_mul_mem_factoredIdeals_insert [DecidableEq (HeightOneSpectrum R)]
    {S : Finset (HeightOneSpectrum R)}
    {v : HeightOneSpectrum R} {I : Ideal R} (hI : I ∈ factoredIdeals S) (k : ℕ) :
    v.asIdeal ^ k * I ∈ factoredIdeals (insert v S) := by
  refine ⟨?_, fun w hw ↦ ?_⟩
  · have hv0 : v.asIdeal ≠ 0 := by simpa [Submodule.zero_eq_bot] using v.ne_bot
    rw [Ne, Ideal.mul_eq_bot, not_or]
    exact ⟨by simpa [Submodule.zero_eq_bot] using pow_ne_zero k hv0, hI.1⟩
  · rcases (HeightOneSpectrum.prime w).dvd_or_dvd hw with h | h
    · rw [heightOneSpectrum_eq_of_dvd_pow h]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hI.2 w h)

theorem pow_mul_inj {v : HeightOneSpectrum R} {k j : ℕ} {I J : Ideal R}
    (hI : ¬ v.asIdeal ∣ I) (hJ : ¬ v.asIdeal ∣ J) (h : v.asIdeal ^ k * I = v.asIdeal ^ j * J) :
    k = j ∧ I = J := by
  have hv0 : v.asIdeal ≠ 0 := by simpa [Submodule.zero_eq_bot] using v.ne_bot
  have hp0 : ∀ n : ℕ, v.asIdeal ^ n ≠ 0 := fun n ↦ pow_ne_zero n hv0
  rcases lt_trichotomy k j with hkj | rfl | hkj
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkj
    rw [add_assoc, pow_add, mul_assoc] at h
    have h' := mul_left_cancel₀ (hp0 k) h
    exact hI (h' ▸ Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero d)) J)
  · exact ⟨rfl, mul_left_cancel₀ (hp0 k) h⟩
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hkj
    rw [add_assoc, pow_add, mul_assoc] at h
    have h' := mul_left_cancel₀ (hp0 j) h.symm
    exact hJ (h' ▸ Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero d)) I)

theorem exists_pow_mul_of_mem_factoredIdeals_insert [DecidableEq (HeightOneSpectrum R)]
    {S : Finset (HeightOneSpectrum R)}
    {v : HeightOneSpectrum R} {I : Ideal R} (hI : I ∈ factoredIdeals (insert v S)) :
    ∃ k : ℕ, ∃ J ∈ factoredIdeals S, I = v.asIdeal ^ k * J := by
  have hI0 : I ≠ 0 := by simpa [Submodule.zero_eq_bot] using hI.1
  have hfin : FiniteMultiplicity v.asIdeal I :=
    FiniteMultiplicity.of_not_isUnit (fun h ↦ v.isPrime.ne_top (Ideal.isUnit_iff.1 h)) hI0
  obtain ⟨J, hJ⟩ := pow_multiplicity_dvd v.asIdeal I
  refine ⟨multiplicity v.asIdeal I, J, ⟨?_, fun w hw ↦ ?_⟩, hJ⟩
  · rintro rfl
    rw [Ideal.mul_bot] at hJ
    exact hI.1 hJ
  · have hwI : w.asIdeal ∣ I := by
      rw [hJ]
      exact dvd_mul_of_dvd_right hw _
    rcases Finset.mem_insert.1 (hI.2 w hwI) with rfl | hw'
    · exfalso
      apply hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
      rw [pow_succ]
      conv_rhs => rw [hJ]
      exact mul_dvd_mul_left _ hw
    · exact hw'

theorem eventually_mem_factoredIdeals {I : Ideal R} (hI : I ≠ ⊥) :
    ∀ᶠ S : Finset (HeightOneSpectrum R) in atTop, I ∈ factoredIdeals S := by
  have hfin := Ideal.finite_factors (I := I) (by simpa [Submodule.zero_eq_bot] using hI)
  refine Filter.eventually_atTop.2 ⟨hfin.toFinset, fun S hS ↦ ⟨hI, fun v hv ↦ hS ?_⟩⟩
  rw [Set.Finite.mem_toFinset]
  exact hv

end Factored

section Euler

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (g : Ideal R →* ℂ)

theorem norm_lt_one_of_summable (hsum : Summable fun I ↦ ‖g I‖) (v : HeightOneSpectrum R) :
    ‖g v.asIdeal‖ < 1 := by
  have hv0 : v.asIdeal ≠ 0 := by simpa [Submodule.zero_eq_bot] using v.ne_bot
  have hinj : Injective fun k : ℕ ↦ v.asIdeal ^ k :=
    pow_injective_of_not_isUnit (fun h ↦ v.isPrime.ne_top (Ideal.isUnit_iff.1 h)) hv0
  have h := hsum.comp_injective hinj
  simp only [Function.comp_def, map_pow, norm_pow] at h
  simpa using summable_geometric_iff_norm_lt_one.1 h

theorem hasSum_indicator_factoredIdeals (hsum : Summable fun I ↦ ‖g I‖)
    (S : Finset (HeightOneSpectrum R)) :
    HasSum ((factoredIdeals S).indicator g) (∏ v ∈ S, (1 - g v.asIdeal)⁻¹) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [factoredIdeals_empty, Finset.prod_empty]
    have h : ({⊤} : Set (Ideal R)).indicator g = fun I ↦ if I = ⊤ then 1 else 0 := by
      ext I
      by_cases h : I = ⊤
      · rw [h, Set.indicator_of_mem (Set.mem_singleton _), if_pos rfl, ← Ideal.one_eq_top,
          map_one]
      · rw [Set.indicator_of_notMem (by simpa using h), if_neg h]
    rw [h]
    exact hasSum_ite_eq ⊤ 1
  | insert v S hv ih =>
    rw [Finset.prod_insert hv]
    have hlt := norm_lt_one_of_summable g hsum v
    have hgeo := hasSum_geometric_of_norm_lt_one hlt
    have hgeo' : Summable fun k : ℕ ↦ ‖g v.asIdeal ^ k‖ := by
      simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hlt
    have hind : Summable fun I ↦ ‖(factoredIdeals S).indicator g I‖ :=
      hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun I ↦ norm_indicator_le_norm_self g I
    have hprod := hgeo.mul ih (summable_mul_of_summable_norm hgeo' hind)
    set F : ℕ × Ideal R → ℂ := fun x ↦ g v.asIdeal ^ x.1 * (factoredIdeals S).indicator g x.2
      with hF
    have hmemF : ∀ x : ℕ × Ideal R, F x ≠ 0 → x.2 ∈ factoredIdeals S := by
      intro x hx
      by_contra h
      apply hx
      simp only [hF, Set.indicator_of_notMem h, mul_zero]
    have hndvd : ∀ {J : Ideal R}, J ∈ factoredIdeals S → ¬ v.asIdeal ∣ J := fun hJ h ↦ hv (hJ.2 v h)
    refine (hasSum_iff_hasSum_of_ne_zero_bij (fun x : support F ↦ v.asIdeal ^ (x : ℕ × Ideal R).1 *
      (x : ℕ × Ideal R).2) ?_ ?_ ?_).2 hprod
    · rintro ⟨⟨k, I⟩, hx⟩ ⟨⟨j, J⟩, hy⟩ h
      obtain ⟨rfl, rfl⟩ := pow_mul_inj (hndvd (hmemF _ hx)) (hndvd (hmemF _ hy)) h
      rfl
    · intro I hI
      rw [mem_support] at hI
      have hI' : I ∈ factoredIdeals (insert v S) := Set.mem_of_indicator_ne_zero hI
      obtain ⟨k, J, hJ, rfl⟩ := exists_pow_mul_of_mem_factoredIdeals_insert hI'
      refine ⟨⟨(k, J), ?_⟩, rfl⟩
      rw [mem_support]
      simp only [hF, Set.indicator_of_mem hJ]
      rwa [Set.indicator_of_mem hI', map_mul, map_pow] at hI
    · rintro ⟨⟨k, J⟩, hx⟩
      have hJ := hmemF _ hx
      simp only [hF]
      rw [Set.indicator_of_mem hJ, Set.indicator_of_mem (pow_mul_mem_factoredIdeals_insert hJ k),
        map_mul, map_pow]

theorem hasProd_euler (hsum : Summable fun I ↦ ‖g I‖) (h0 : g ⊥ = 0) :
    HasProd (fun v : HeightOneSpectrum R ↦ (1 - g v.asIdeal)⁻¹) (∑' I, g I) := by
  have key : (fun S : Finset (HeightOneSpectrum R) ↦ ∏ v ∈ S, (1 - g v.asIdeal)⁻¹) =
      fun S ↦ ∑' I, (factoredIdeals S).indicator g I :=
    funext fun S ↦ (hasSum_indicator_factoredIdeals g hsum S).tsum_eq.symm
  show Tendsto (fun S : Finset (HeightOneSpectrum R) ↦ ∏ v ∈ S, (1 - g v.asIdeal)⁻¹) atTop
    (𝓝 (∑' I, g I))
  rw [key]
  refine tendsto_tsum_of_dominated_convergence hsum (fun I ↦ ?_)
    (Eventually.of_forall fun S I ↦ norm_indicator_le_norm_self g I)
  by_cases hI : I = ⊥
  · subst hI
    have : ∀ S : Finset (HeightOneSpectrum R), (factoredIdeals S).indicator g ⊥ = g ⊥ :=
      fun S ↦ by rw [Set.indicator_of_notMem (fun h ↦ h.1 rfl), h0]
    simp only [this]
    exact tendsto_const_nhds
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_factoredIdeals hI] with S hS
    rw [Set.indicator_of_mem hS]

end Euler

section Summable

variable {K : Type*} [Field K] [NumberField K]

theorem exists_tendsto_sum_card_absNorm_div :
    ∃ l : ℝ, Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ)) / n) atTop (𝓝 l) := by
  refine ⟨_, ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n ↦ ?_⟩
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem LSeriesSummable_card_absNorm {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℂ)) s := by
  obtain ⟨l, hl⟩ := exists_tendsto_sum_card_absNorm_div (K := K)
  refine LSeriesSummable_of_sum_norm_bigO (r := 1) ?_ zero_le_one hs
  have h1 := (hl.isBigO_one ℝ).mul (Asymptotics.isBigO_refl (fun n : ℕ ↦ (n : ℝ)) atTop)
  refine h1.congr' ?_ ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Complex.norm_natCast]
    rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.2 hn)]
  · exact Eventually.of_forall fun n ↦ by simp

theorem summable_absNorm_rpow_inv {σ : ℝ} (hσ : 1 < σ) :
    Summable fun I : Ideal (𝓞 K) ↦ ((absNorm I : ℝ) ^ σ)⁻¹ :=
  _root_.UpperTheory.Reformulated.B.Qp7.summable_absNorm_rpow_inv hσ

end Summable

section Coprime

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
theorem not_dvd_of_isCoprime {I 𝔪 : Ideal (𝓞 K)} (h : IsCoprime I 𝔪)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪) : ¬ v.asIdeal ∣ I := by
  intro hI
  rw [Ideal.isCoprime_iff_sup_eq] at h
  exact v.isPrime.ne_top (top_le_iff.1 (h ▸ sup_le (Ideal.le_of_dvd hI) (Ideal.le_of_dvd hv)))

theorem isCoprime_asIdeal_iff (v : HeightOneSpectrum (𝓞 K)) (𝔪 : Ideal (𝓞 K)) :
    IsCoprime v.asIdeal 𝔪 ↔ ¬ v.asIdeal ∣ 𝔪 := by
  constructor
  · intro h hv
    exact not_dvd_of_isCoprime h hv (dvd_refl _)
  · intro h
    rw [Ideal.isCoprime_iff_sup_eq]
    exact v.isMaximal.out.2 _ (left_lt_sup.2 fun hle ↦ h (Ideal.dvd_iff_le.2 hle))

theorem count_coeIdeal_eq_zero {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ I) : count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  classical
  have hI0 : I ≠ 0 := by simpa [Submodule.zero_eq_bot] using hI
  rw [count_coe K v hI0, Nat.cast_eq_zero]
  by_contra h
  exact hv ((Associates.count_ne_zero_iff_dvd hI0 (HeightOneSpectrum.prime v).irreducible).1 h)

def idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (coeIdeal_ne_zero.2 hI)

theorem idealUnit_mem_idealsPrimeTo {I 𝔪 : Ideal (𝓞 K)} (hI : I ≠ ⊥) (h : IsCoprime I 𝔪) :
    idealUnit I hI ∈ idealsPrimeTo 𝔪 :=
  fun _ hv ↦ count_coeIdeal_eq_zero hI (not_dvd_of_isCoprime h hv)

end Coprime

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)

open Classical in

def coeff (I : Ideal (𝓞 K)) : ℂ :=
  if h : I ≠ ⊥ ∧ IsCoprime I χ.conductor then
    (χ.idealCharacter ⟨idealUnit I h.1, idealUnit_mem_idealsPrimeTo h.1 h.2⟩ : ℂ)
  else 0

theorem coeff_of_mem {I : Ideal (𝓞 K)} (h : I ≠ ⊥ ∧ IsCoprime I χ.conductor) :
    χ.coeff I = χ.idealCharacter ⟨idealUnit I h.1, idealUnit_mem_idealsPrimeTo h.1 h.2⟩ :=
  dif_pos h

theorem coeff_of_not {I : Ideal (𝓞 K)} (h : ¬ (I ≠ ⊥ ∧ IsCoprime I χ.conductor)) :
    χ.coeff I = 0 :=
  dif_neg h

@[simp]
theorem coeff_bot : χ.coeff ⊥ = 0 :=
  χ.coeff_of_not fun h ↦ h.1 rfl

theorem norm_coeff_le (I : Ideal (𝓞 K)) : ‖χ.coeff I‖ ≤ 1 := by
  unfold coeff
  split_ifs
  · rw [Circle.norm_coe]
  · simp

@[simp]
theorem coeff_top : χ.coeff ⊤ = 1 := by
  have h : (⊤ : Ideal (𝓞 K)) ≠ ⊥ ∧ IsCoprime (⊤ : Ideal (𝓞 K)) χ.conductor :=
    ⟨top_ne_bot, by rw [← Ideal.one_eq_top]; exact isCoprime_one_left⟩
  rw [coeff, dif_pos h]
  have h1 : (⟨idealUnit ⊤ h.1, idealUnit_mem_idealsPrimeTo h.1 h.2⟩ : idealsPrimeTo χ.conductor) =
      1 :=
    Subtype.ext (Units.ext (by simp [idealUnit]))
  rw [h1, map_one, Circle.coe_one]

theorem coeff_mul (I J : Ideal (𝓞 K)) : χ.coeff (I * J) = χ.coeff I * χ.coeff J := by
  by_cases hI : I ≠ ⊥ ∧ IsCoprime I χ.conductor
  · by_cases hJ : J ≠ ⊥ ∧ IsCoprime J χ.conductor
    · have hIJ : I * J ≠ ⊥ ∧ IsCoprime (I * J) χ.conductor :=
        ⟨fun h ↦ (Ideal.mul_eq_bot.1 h).elim hI.1 hJ.1, hI.2.mul_left hJ.2⟩
      rw [coeff, coeff, coeff, dif_pos hI, dif_pos hJ, dif_pos hIJ, ← Circle.coe_mul, ← map_mul]
      congr 2
      exact Subtype.ext (Units.ext (by simp [idealUnit, coeIdeal_mul]))
    · rw [χ.coeff_of_not hJ, mul_zero]
      refine χ.coeff_of_not fun h ↦ hJ ⟨fun hJ0 ↦ h.1 (by rw [hJ0, Ideal.mul_bot]), ?_⟩
      exact (IsCoprime.mul_left_iff.1 h.2).2
  · rw [χ.coeff_of_not hI, zero_mul]
    refine χ.coeff_of_not fun h ↦ hI ⟨fun hI0 ↦ h.1 (by rw [hI0, Ideal.bot_mul]), ?_⟩
    exact (IsCoprime.mul_left_iff.1 h.2).1

theorem coeff_asIdeal_of_dvd {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ χ.conductor) :
    χ.coeff v.asIdeal = 0 :=
  χ.coeff_of_not fun h ↦ ((isCoprime_asIdeal_iff v _).1 h.2) hv

theorem coeff_asIdeal_of_not_dvd {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ χ.conductor) :
    χ.coeff v.asIdeal =
      χ.idealCharacter ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ := by
  rw [coeff, dif_pos ⟨v.ne_bot, (isCoprime_asIdeal_iff v _).2 hv⟩]
  rfl

def coeffTerm (s : ℂ) : Ideal (𝓞 K) →* ℂ where
  toFun I := χ.coeff I / (absNorm I : ℂ) ^ s
  map_one' := by
    rw [Ideal.one_eq_top, coeff_top, Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow, _root_.div_one]
  map_mul' I J := by
    rw [coeff_mul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, mul_div_mul_comm]

theorem coeffTerm_apply (s : ℂ) (I : Ideal (𝓞 K)) :
    χ.coeffTerm s I = χ.coeff I / (absNorm I : ℂ) ^ s :=
  rfl

@[simp]
theorem coeffTerm_bot (s : ℂ) : χ.coeffTerm s ⊥ = 0 := by
  rw [coeffTerm_apply, coeff_bot, zero_div]

theorem norm_coeffTerm_le {s : ℂ} (I : Ideal (𝓞 K)) :
    ‖χ.coeffTerm s I‖ ≤ ((absNorm I : ℝ) ^ s.re)⁻¹ := by
  by_cases hI : I = ⊥
  · subst hI
    rw [coeffTerm_bot, norm_zero]
    exact inv_nonneg.2 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · have hpos : 0 < absNorm I := Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
    rw [coeffTerm_apply, norm_div, Complex.norm_natCast_cpow_of_pos hpos, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (χ.norm_coeff_le I) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem summable_norm_coeffTerm {s : ℂ} (hs : 1 < s.re) :
    Summable fun I ↦ ‖χ.coeffTerm s I‖ :=
  (summable_absNorm_rpow_inv hs).of_nonneg_of_le (fun _ ↦ norm_nonneg _) χ.norm_coeffTerm_le

def LCoeff (n : ℕ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, χ.coeff I

def LFunction (s : ℂ) : ℂ :=
  LSeries χ.LCoeff s

theorem hasSum_term_LCoeff {s : ℂ} (hs : 1 < s.re) :
    HasSum (LSeries.term χ.LCoeff s) (∑' I, χ.coeffTerm s I) := by
  have hsum : Summable (χ.coeffTerm s) := (χ.summable_norm_coeffTerm hs).of_norm
  let e := Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) ↦ absNorm I)
  have h1 : HasSum (χ.coeffTerm s ∘ e) (∑' I, χ.coeffTerm s I) := e.hasSum_iff.2 hsum.hasSum
  have h2 := h1.sigma fun n ↦ ((e.summable_iff.2 hsum).sigma_factor n).hasSum
  convert h2 using 1
  funext n
  rw [LSeries.term_def]
  split_ifs with hn
  · subst hn
    symm
    refine (tsum_congr fun y ↦ ?_).trans tsum_zero
    have hy : (y : Ideal (𝓞 K)) = ⊥ := Ideal.absNorm_eq_zero_iff.1 y.2
    simp [e, hy]
  · rw [LCoeff, ← tsum_div_const]
    refine tsum_congr fun y ↦ ?_
    simp [e, coeffTerm_apply, y.2]

theorem LSeriesSummable_LCoeff {s : ℂ} (hs : 1 < s.re) : LSeriesSummable χ.LCoeff s :=
  (χ.hasSum_term_LCoeff hs).summable

theorem LFunction_eq_tsum_coeffTerm {s : ℂ} (hs : 1 < s.re) :
    χ.LFunction s = ∑' I, χ.coeffTerm s I :=
  (χ.hasSum_term_LCoeff hs).tsum_eq

theorem summable_norm_coeff_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) ↦ ‖χ.coeff I * (absNorm I : ℂ) ^ (-s)‖ := by
  simpa [coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv] using χ.summable_norm_coeffTerm hs

theorem hasSum_LFunction {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : Ideal (𝓞 K) ↦ χ.coeff I * (absNorm I : ℂ) ^ (-s)) (χ.LFunction s) := by
  have hfun : (fun I : Ideal (𝓞 K) ↦ χ.coeff I * (absNorm I : ℂ) ^ (-s)) = χ.coeffTerm s :=
    funext fun I ↦ by rw [coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]
  rw [χ.LFunction_eq_tsum_coeffTerm hs, hfun]
  exact ((χ.summable_norm_coeffTerm hs).of_norm).hasSum

theorem hasSum_LFunction_coprime {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦
      (χ.idealCharacter ⟨idealUnit I.1 I.2.1, idealUnit_mem_idealsPrimeTo I.2.1 I.2.2⟩ : ℂ) *
        (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) (χ.LFunction s) := by
  have h := χ.hasSum_LFunction hs
  rw [← hasSum_subtype_iff_of_support_subset (s := {I | I ≠ ⊥ ∧ IsCoprime I χ.conductor})] at h
  · have h2 : HasSum (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦
        χ.coeff I.1 * (absNorm I.1 : ℂ) ^ (-s)) (χ.LFunction s) := h
    have hfun : (fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦
        (χ.idealCharacter ⟨idealUnit I.1 I.2.1, idealUnit_mem_idealsPrimeTo I.2.1 I.2.2⟩ : ℂ) *
          (absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
        fun I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I χ.conductor} ↦
          χ.coeff I.1 * (Ideal.absNorm I.1 : ℂ) ^ (-s) :=
      funext fun I ↦ by rw [χ.coeff_of_mem I.2]
    rw [hfun]
    exact h2
  · intro I hI
    by_contra h'
    exact hI (by simp only [χ.coeff_of_not h', zero_mul])

theorem abscissaOfAbsConv_LCoeff_le : LSeries.abscissaOfAbsConv χ.LCoeff ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
    χ.LSeriesSummable_LCoeff (by simpa using hy)

theorem differentiableOn_LFunction : DifferentiableOn ℂ χ.LFunction {s | 1 < s.re} :=
  (LSeries_differentiableOn χ.LCoeff).mono fun s hs ↦
    χ.abscissaOfAbsConv_LCoeff_le.trans_lt (by exact_mod_cast hs)

theorem analyticOnNhd_LFunction : AnalyticOnNhd ℂ χ.LFunction {s | 1 < s.re} :=
  (LSeries_analyticOnNhd χ.LCoeff).mono fun s hs ↦
    χ.abscissaOfAbsConv_LCoeff_le.trans_lt (by exact_mod_cast hs)

theorem LFunction_hasProd_all {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) ↦
      (1 - χ.coeff v.asIdeal * (absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (χ.LFunction s) := by
  rw [χ.LFunction_eq_tsum_coeffTerm hs]
  convert hasProd_euler (χ.coeffTerm s) (χ.summable_norm_coeffTerm hs) (χ.coeffTerm_bot s)
    using 3 with v
  rw [coeffTerm_apply, Complex.cpow_neg, div_eq_mul_inv]

theorem LFunction_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦
      (1 - (χ.idealCharacter ⟨primeIdealUnit v.1, primeIdealUnit_mem_idealsPrimeTo v.2⟩ : ℂ) *
        (absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) (χ.LFunction s) := by
  have h := χ.LFunction_hasProd_all hs
  rw [← hasProd_subtype_iff_of_mulSupport_subset
    (s := {v : HeightOneSpectrum (𝓞 K) | ¬ v.asIdeal ∣ χ.conductor})] at h
  · have h2 : HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦
        (1 - χ.coeff v.1.asIdeal * (absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) (χ.LFunction s) := h
    have hfun : (fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦
        (1 - (χ.idealCharacter ⟨primeIdealUnit v.1, primeIdealUnit_mem_idealsPrimeTo v.2⟩ : ℂ) *
          (absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) =
        fun v : {v : HeightOneSpectrum (𝓞 K) // ¬ v.asIdeal ∣ χ.conductor} ↦
          (1 - χ.coeff v.1.asIdeal * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ :=
      funext fun v ↦ by rw [χ.coeff_asIdeal_of_not_dvd v.2]
    rw [hfun]
    exact h2
  · intro v hv
    by_contra hdvd
    have hdvd' : v.asIdeal ∣ χ.conductor := by simpa using hdvd
    apply hv
    simp only [χ.coeff_asIdeal_of_dvd hdvd', zero_mul, sub_zero, inv_one]

theorem LFunction_ne_zero {s : ℂ} (hs : 1 < s.re) : χ.LFunction s ≠ 0 := by
  set x : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ χ.coeffTerm s v.asIdeal with hx
  have hlt : ∀ v, ‖x v‖ < 1 := fun v ↦ norm_lt_one_of_summable _ (χ.summable_norm_coeffTerm hs) v
  have hne : ∀ v, 1 - x v ≠ 0 := by
    intro v h
    have h1 : x v = 1 := (sub_eq_zero.1 h).symm
    have h2 := hlt v
    rw [h1, norm_one] at h2
    exact lt_irrefl _ h2
  have hinj : Injective fun v : HeightOneSpectrum (𝓞 K) ↦ v.asIdeal :=
    fun v w h ↦ HeightOneSpectrum.ext h
  have hxs : Summable x :=
    Summable.of_norm (f := x) ((χ.summable_norm_coeffTerm hs).comp_injective hinj)
  have hlog : Summable fun v ↦ Complex.log (1 - x v) :=
    (Complex.summable_log_one_add_of_summable hxs.neg).congr fun v ↦ by rw [sub_eq_add_neg]
  have hP : HasProd (fun v ↦ 1 - x v) (Complex.exp (∑' v, Complex.log (1 - x v))) :=
    Complex.hasProd_of_hasSum_log hne hlog.hasSum
  have hL : HasProd (fun v ↦ (1 - x v)⁻¹) (χ.LFunction s) := by
    rw [χ.LFunction_eq_tsum_coeffTerm hs]
    exact hasProd_euler _ (χ.summable_norm_coeffTerm hs) (χ.coeffTerm_bot s)
  have h1 := hL.mul hP
  have h2 : (fun v ↦ (1 - x v)⁻¹ * (1 - x v)) = fun _ ↦ (1 : ℂ) :=
    funext fun v ↦ inv_mul_cancel₀ (hne v)
  rw [h2] at h1
  have h3 := h1.unique hasProd_one
  intro hL0
  rw [hL0, zero_mul] at h3
  exact zero_ne_one h3

theorem conductor_one : (1 : HeckeCharacter K).conductor = ⊤ := by
  have h : ∀ v, IdeleGroup.conductorExponentAt
      ((1 : HeckeCharacter K).toIdele.comp IdeleGroup.ofFinite) v = 0 := fun v ↦
    (IdeleGroup.conductorExponentAt_eq_zero_iff Circle.noSmallSubgroups _
      ((1 : HeckeCharacter K).continuous_toIdele.comp IdeleGroup.continuous_ofFinite) v).2
      fun x _ ↦ by rw [MonoidHom.mem_ker]; rfl
  rw [conductor, IdeleGroup.conductor]
  simp only [h, pow_zero]
  rw [finprod_one, Ideal.one_eq_top]

theorem coeff_one {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : (1 : HeckeCharacter K).coeff I = 1 := by
  have h : I ≠ ⊥ ∧ IsCoprime I (1 : HeckeCharacter K).conductor :=
    ⟨hI, by rw [conductor_one, ← Ideal.one_eq_top]; exact isCoprime_one_right⟩
  rw [coeff, dif_pos h]
  exact congrArg ((↑) : Circle → ℂ) rfl |>.trans Circle.coe_one

theorem LFunction_one (s : ℂ) : (1 : HeckeCharacter K).LFunction s = dedekindZeta K s := by
  rw [LFunction, dedekindZeta]
  refine LSeries_congr (fun {n} hn ↦ ?_) s
  have hy : ∀ y : {I : Ideal (𝓞 K) // absNorm I = n}, (1 : HeckeCharacter K).coeff y = 1 := by
    intro y
    refine coeff_one fun h ↦ hn ?_
    rw [← y.2, h, Ideal.absNorm_bot]
  rw [LCoeff, tsum_congr hy, tsum_const, nsmul_eq_mul, mul_one]

end HeckeCharacter

end

end GroundTheory.Global

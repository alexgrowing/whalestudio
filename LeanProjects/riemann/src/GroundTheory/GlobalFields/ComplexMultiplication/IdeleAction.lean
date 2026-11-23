import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem le_one_of_forall_count_nonneg {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ count K v I) : I ≤ 1 := by
  rw [← finprod_heightOneSpectrum_factorization' (K := K) hI]
  refine finprod_induction (· ≤ 1) le_rfl (fun a b ha hb ↦ ?_) fun v ↦ ?_
  · calc a * b ≤ 1 * b := mul_le_mul_left ha b
      _ = b := one_mul b
      _ ≤ 1 := hb
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
    rw [hn, zpow_natCast, ← coeIdeal_pow]
    exact coeIdeal_le_one

theorem le_iff_forall_count_le {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J ↔ ∀ v : HeightOneSpectrum (𝓞 K), count K v J ≤ count K v I := by
  refine ⟨fun h v ↦ count_mono K v hI h, fun h ↦ ?_⟩
  have hJ' : J⁻¹ ≠ 0 := inv_ne_zero hJ
  have hle : I * J⁻¹ ≤ 1 := le_one_of_forall_count_nonneg (mul_ne_zero hI hJ') fun v ↦ by
    rw [count_mul K v hI hJ', count_inv]
    linarith [h v]
  calc I = I * J⁻¹ * J := by rw [mul_assoc, inv_mul_cancel₀ hJ, mul_one]
    _ ≤ 1 * J := mul_le_mul_left hle J
    _ = J := one_mul J

theorem mem_iff_forall_valuation_le {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {x : K} :
    x ∈ I ↔ ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K x ≤ exp (-count K v I) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact iff_of_true (FractionalIdeal.zero_mem I) fun v ↦ by simp only [map_zero, _root_.zero_le]
  have hs : spanSingleton (𝓞 K)⁰ x ≠ 0 := spanSingleton_ne_zero_iff.2 hx
  rw [← spanSingleton_le_iff_mem, le_iff_forall_count_le hs hI]
  refine forall_congr' fun v ↦ ?_
  have hv : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  rw [count_spanSingleton v hx, le_neg, ← log_le_iff_le_exp hv]

theorem le_exp_sub_one_of_lt {y : ℤᵐ⁰} {n : ℤ} (h : y < exp n) : y ≤ exp (n - 1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact zero_le
  rw [← log_le_iff_le_exp hy]
  have := (log_lt_iff_lt_exp hy).2 h
  omega

theorem exists_mem_valuation_eq {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) : ∃ a ∈ I, v.valuation K a = exp (-count K v I) := by
  set P : FractionalIdeal (𝓞 K)⁰ K := (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) with hPdef
  have hP : P ≠ 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have hIP : I * P ≠ 0 := mul_ne_zero hI hP
  have hne : ¬ I ≤ I * P := fun h ↦ by
    have := count_mono K v hI h
    rw [count_mul K v hI hP, hPdef, count_self] at this
    omega
  obtain ⟨a, haI, haIP⟩ := SetLike.not_le_iff_exists.1 hne
  refine ⟨a, haI, le_antisymm ((mem_iff_forall_valuation_le hI).1 haI v) ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  apply haIP
  rw [mem_iff_forall_valuation_le hIP]
  intro w
  rw [count_mul K w hI hP]
  by_cases hw : w = v
  · subst hw
    rw [hPdef, count_self, show -(count K w I + 1) = -count K w I - 1 by ring]
    exact le_exp_sub_one_of_lt hlt
  · rw [hPdef, count_maximal_coprime K w (Ne.symm hw), add_zero]
    exact (mem_iff_forall_valuation_le hI).1 haI w

def localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) (v : HeightOneSpectrum (𝓞 K)) :
    Submodule (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Submodule.span _ ((fun x : K ↦ (x : v.adicCompletion K)) '' (I : Set K))

theorem coe_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (v : HeightOneSpectrum (𝓞 K)) {x : K}
    (hx : x ∈ I) : (x : v.adicCompletion K) ∈ localIdeal I v :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem mem_localIdeal_iff {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) {y : v.adicCompletion K} :
    y ∈ localIdeal I v ↔ Valued.v y ≤ exp (-count K v I) := by
  constructor
  · intro hy
    refine Submodule.span_induction (p := fun y _ ↦ Valued.v y ≤ exp (-count K v I)) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨x, hx, rfl⟩
      rw [valuedAdicCompletion_eq_valuation']
      exact (mem_iff_forall_valuation_le hI).1 hx v
    · simp only [map_zero, _root_.zero_le]
    · intro a b _ _ ha hb
      exact (Valuation.map_add _ a b).trans (max_le ha hb)
    · intro r a _ ha
      change Valued.v ((r : v.adicCompletion K) * a) ≤ _
      rw [map_mul]
      exact (mul_le_of_le_one_left' r.2).trans ha
  · intro hy
    obtain ⟨a, haI, ha⟩ := exists_mem_valuation_eq hI v
    have ha' : Valued.v (a : v.adicCompletion K) = exp (-count K v I) := by
      rw [valuedAdicCompletion_eq_valuation', ha]
    have ha0 : (a : v.adicCompletion K) ≠ 0 := by
      intro h
      rw [h, map_zero] at ha'
      exact exp_ne_zero ha'.symm
    have hr : y / a ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers, map_div₀, ha']
      exact div_le_one_of_le₀ hy _root_.zero_le
    have hy' : y = (⟨y / a, hr⟩ : v.adicCompletionIntegers K) • (a : v.adicCompletion K) := by
      change y = y / a * a
      rw [div_mul_cancel₀ _ ha0]
    rw [hy']
    exact Submodule.smul_mem _ _ (coe_mem_localIdeal v haI)

theorem mem_iff_forall_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) {x : K} :
    x ∈ I ↔ ∀ v : HeightOneSpectrum (𝓞 K), (x : v.adicCompletion K) ∈ localIdeal I v := by
  rw [mem_iff_forall_valuation_le hI]
  refine forall_congr' fun v ↦ ?_
  rw [mem_localIdeal_iff hI, valuedAdicCompletion_eq_valuation']

theorem mem_localIdeal_one_iff (v : HeightOneSpectrum (𝓞 K)) {y : v.adicCompletion K} :
    y ∈ localIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) v ↔ y ∈ v.adicCompletionIntegers K := by
  have h1 : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    simpa only [Units.val_one] using (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ).ne_zero
  rw [mem_localIdeal_iff h1, count_one, neg_zero, exp_zero, mem_adicCompletionIntegers]

theorem eq_of_localIdeal_eq {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), localIdeal I v = localIdeal J v) : I = J := by
  ext x
  rw [mem_iff_forall_mem_localIdeal hI, mem_iff_forall_mem_localIdeal hJ]
  simp only [h]

theorem eventually_coe_mem_localIdeal {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (x : K) :
    ∀ᶠ v in Filter.cofinite, (x : v.adicCompletion K) ∈ localIdeal I v := by
  have h1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, count K v I = 0 :=
    FractionalIdeal.finite_factors (K := K) I
  have h2 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (x : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) x).2
  filter_upwards [h1, h2] with v hv1 hv2
  rw [mem_localIdeal_iff hI, hv1, neg_zero, exp_zero]
  exact hv2

namespace IdeleGroup

local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ

theorem valued_eq_exp_neg_ord (v : HeightOneSpectrum (𝓞 K)) (s : IdeleGroup K) :
    Valued.v ((s : 𝔸[K]).2 v) = exp (-ord v s) := by
  rw [ord, neg_neg, exp_log (valued_ne_zero v s)]

theorem component_ne_zero (v : HeightOneSpectrum (𝓞 K)) (s : IdeleGroup K) :
    (s : 𝔸[K]).2 v ≠ 0 :=
  (Valuation.ne_zero_iff _).1 (valued_ne_zero v s)

instance : MulAction (IdeleGroup K) 𝓘 where
  smul s I := toFractionalIdeal s * I
  one_smul I := by
    change toFractionalIdeal 1 * I = I
    rw [map_one, one_mul]
  mul_smul s t I := by
    change toFractionalIdeal (s * t) * I = toFractionalIdeal s * (toFractionalIdeal t * I)
    rw [map_mul, mul_assoc]

theorem smul_def (s : IdeleGroup K) (I : 𝓘) : s • I = toFractionalIdeal s * I :=
  rfl

theorem smul_one_eq_toFractionalIdeal (s : IdeleGroup K) : s • (1 : 𝓘) = toFractionalIdeal s :=
  mul_one _

instance : IsScalarTower (IdeleGroup K) 𝓘 𝓘 :=
  ⟨fun s I J ↦ by simp only [smul_def, smul_eq_mul, mul_assoc]⟩

instance : SMulCommClass (IdeleGroup K) 𝓘 𝓘 :=
  ⟨fun s I J ↦ by simp only [smul_def, smul_eq_mul, mul_left_comm]⟩

theorem smul_mul_eq (s : IdeleGroup K) (I J : 𝓘) : s • (I * J) = s • I * J :=
  (mul_assoc _ _ _).symm

theorem smul_inv_eq (s : IdeleGroup K) (I : 𝓘) : (s • I)⁻¹ = s⁻¹ • I⁻¹ := by
  rw [smul_def, smul_def, mul_inv, map_inv]

theorem count_smul (v : HeightOneSpectrum (𝓞 K)) (s : IdeleGroup K) (I : 𝓘) :
    count K v ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) =
      ord v s + count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [smul_def, Units.val_mul, count_mul K v (Units.ne_zero _) (Units.ne_zero _),
    count_toFractionalIdeal]

theorem smul_le_smul_iff {s : IdeleGroup K} {I J : 𝓘} :
    ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) ≤ (s • J : 𝓘) ↔
      (I : FractionalIdeal (𝓞 K)⁰ K) ≤ J := by
  rw [le_iff_forall_count_le (Units.ne_zero _) (Units.ne_zero _),
    le_iff_forall_count_le (Units.ne_zero _) (Units.ne_zero _)]
  simp only [count_smul, add_le_add_iff_left]

instance : MulAction.IsPretransitive (IdeleGroup K) 𝓘 :=
  ⟨fun I J ↦ by
    obtain ⟨s, hs⟩ := toFractionalIdeal_surjective (J * I⁻¹)
    exact ⟨s, by rw [smul_def, hs, inv_mul_cancel_right]⟩⟩

theorem smul_eq_smul_iff {s t : IdeleGroup K} {I : 𝓘} :
    s • I = t • I ↔ toFractionalIdeal s = toFractionalIdeal t := by
  rw [smul_def, smul_def, mul_left_inj]

theorem smul_eq_self_iff {s : IdeleGroup K} {I : 𝓘} :
    s • I = I ↔ s ∈ standardOpenSubgroup K := by
  rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, smul_def, mul_eq_right]

theorem stabilizer_eq (I : 𝓘) :
    MulAction.stabilizer (IdeleGroup K) I = standardOpenSubgroup K := by
  ext s
  exact smul_eq_self_iff

theorem diagonal_smul (a : Kˣ) (I : 𝓘) :
    diagonal K a • I = toPrincipalIdeal (𝓞 K) K a * I := by
  rw [smul_def, toFractionalIdeal_diagonal]

theorem coe_diagonal_smul (a : Kˣ) (I : 𝓘) :
    ((diagonal K a • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ (a : K) * I := by
  rw [diagonal_smul, Units.val_mul, coe_toPrincipalIdeal]

theorem localIdeal_smul (s : IdeleGroup K) (I : 𝓘) (v : HeightOneSpectrum (𝓞 K)) :
    localIdeal ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v =
      (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v).map
        (LinearMap.mulLeft (v.adicCompletionIntegers K) ((s : 𝔸[K]).2 v)) := by
  ext y
  rw [mem_localIdeal_iff (Units.ne_zero _), Submodule.mem_map, count_smul]
  have ht := component_ne_zero v s
  constructor
  · intro hy
    refine ⟨((s : 𝔸[K]).2 v)⁻¹ * y, ?_, ?_⟩
    · rw [mem_localIdeal_iff (Units.ne_zero _), map_mul, map_inv₀, valued_eq_exp_neg_ord]
      calc (exp (-ord v s))⁻¹ * Valued.v y
          ≤ (exp (-ord v s))⁻¹ * exp (-(ord v s + count K v (I : FractionalIdeal (𝓞 K)⁰ K))) :=
            mul_le_mul_right hy _
        _ = exp (-count K v (I : FractionalIdeal (𝓞 K)⁰ K)) := by
            rw [← exp_neg, neg_neg, ← exp_add]
            congr 1
            ring
    · rw [LinearMap.mulLeft_apply, mul_inv_cancel_left₀ ht]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_localIdeal_iff (Units.ne_zero _)] at hz
    rw [LinearMap.mulLeft_apply, map_mul, valued_eq_exp_neg_ord, neg_add, exp_add]
    exact mul_le_mul_right hz _

theorem mem_smul_iff (s : IdeleGroup K) (I : 𝓘) {x : K} :
    x ∈ ((s • I : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      (x : v.adicCompletion K) ∈ (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v).map
        (LinearMap.mulLeft (v.adicCompletionIntegers K) ((s : 𝔸[K]).2 v)) := by
  rw [mem_iff_forall_mem_localIdeal (Units.ne_zero _)]
  simp only [localIdeal_smul]

theorem smul_eq_iff_localIdeal (s : IdeleGroup K) (I J : 𝓘) :
    s • I = J ↔ ∀ v : HeightOneSpectrum (𝓞 K), localIdeal (J : FractionalIdeal (𝓞 K)⁰ K) v =
      (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v).map
        (LinearMap.mulLeft (v.adicCompletionIntegers K) ((s : 𝔸[K]).2 v)) := by
  constructor
  · rintro rfl v
    exact localIdeal_smul s I v
  · intro h
    refine Units.ext (eq_of_localIdeal_eq (Units.ne_zero _) (Units.ne_zero _) fun v ↦ ?_)
    rw [localIdeal_smul, h]

theorem localIdeal_toFractionalIdeal (s : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    localIdeal ((toFractionalIdeal s : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v =
      (localIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) v).map
        (LinearMap.mulLeft (v.adicCompletionIntegers K) ((s : 𝔸[K]).2 v)) := by
  rw [← smul_one_eq_toFractionalIdeal, localIdeal_smul, Units.val_one]

end IdeleGroup

end

end GroundTheory.Global

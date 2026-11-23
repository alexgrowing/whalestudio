import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense

noncomputable section

open NumberField IsDedekindDomain Topology Filter

namespace GlobalTheory.HeckeSplitAll.Approx

variable {F : Type} [Field F] [NumberField F]

theorem norm_alg_inf (w : InfinitePlace F) (x : F) : ‖algebraMap F w.Completion x‖ = w x := by
  rw [show algebraMap F w.Completion x = (x : w.Completion) from rfl]
  simp only [InfinitePlace.Completion.norm_ofCompletion, UniformSpace.Completion.norm_coe]; rfl

theorem norm_le_one_iff_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [Valued.toNormedField.norm_le_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]

theorem norm_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) : ‖(m : v.adicCompletion F)‖ ≤ 1 :=
  (norm_le_one_iff_int v _).2 (natCast_mem _ m)

theorem norm_int_le_one (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ ≤ 1 :=
  (norm_le_one_iff_int v _).2 (PI.UnipApproxD.IntegersDenseFiniteAdeles.int_R v o)

theorem norm_int_eq_one (v : HeightOneSpectrum (𝓞 F)) (o : 𝓞 F) (ho : o ∉ v.asIdeal) :
    ‖algebraMap F (v.adicCompletion F) (o : F)‖ = 1 := by
  refine le_antisymm (norm_int_le_one v o) (not_lt.1 fun h => ho ?_)
  rw [Valued.toNormedField.norm_lt_one_iff] at h
  have e := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R (K := F) v o
  rw [show algebraMap F (v.adicCompletion F) (o : F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F o) from rfl,
    e] at h
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v o).1 h

theorem nat_ne_zero_fin (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (hm : m ≠ 0) : (m : v.adicCompletion F) ≠ 0 := by
  have h := (algebraMap F (v.adicCompletion F)).injective.ne (Nat.cast_ne_zero.2 hm : (m : F) ≠ 0)
  rwa [map_natCast, map_zero] at h

theorem norm_natCast_lt_one (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : (c : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  have hval := (HeightOneSpectrum.intValuation_lt_one_iff_mem v (c : 𝓞 F)).2 hmem
  rw [Valued.toNormedField.norm_lt_one_iff]
  have e := PI.UnipApproxD.IntegersDenseFiniteAdeles.val_R (K := F) v (c : 𝓞 F)
  rw [map_natCast, map_natCast] at e
  rw [e]
  exact hval

theorem exists_finset_norm_one (x : F) (hx : x ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S, ‖algebraMap F (v.adicCompletion F) x‖ = 1 := by
  classical
  have h1 := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  have h2 := Filter.eventually_cofinite.mp (algebraMap F (FiniteAdeleRing (𝓞 F) F) x⁻¹).2
  refine ⟨(h1.union h2).toFinset, fun v hv => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv
  obtain ⟨ha, hb⟩ := hv
  have ha' : ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := (norm_le_one_iff_int v _).2 ha
  have hb' : ‖algebraMap F (v.adicCompletion F) x⁻¹‖ ≤ 1 := (norm_le_one_iff_int v _).2 hb
  rw [map_inv₀, norm_inv] at hb'
  have hpos : 0 < ‖algebraMap F (v.adicCompletion F) x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
  have hm := mul_inv_cancel₀ hpos.ne'
  refine le_antisymm ha' ?_
  nlinarith [mul_nonneg hpos.le (sub_nonneg.2 hb')]

theorem exists_nat_small (x : F) (hx : x ≠ 0) : ∃ P : ℕ, P ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F),
    ‖algebraMap F (v.adicCompletion F) x‖ ≠ 1 → ‖(P : v.adicCompletion F)‖ < 1 := by
  classical
  obtain ⟨B, hB⟩ := exists_finset_norm_one x hx
  refine ⟨∏ v ∈ B, Ideal.absNorm v.asIdeal, ?_, fun v hv => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'
  · exact norm_natCast_lt_one v _ (Finset.dvd_prod_of_mem _ (by_contra fun h => hv (hB v h)))

theorem exists_int_near (F : Type) [Field F] [NumberField F] : ∃ C : ℝ, 0 < C ∧ ∀ t : InfiniteAdeleRing F,
    ∃ o : 𝓞 F, ∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o : F) - t w‖ < C := by
  classical
  set b := integralBasis F with hb
  refine ⟨1 + ∑ w : InfinitePlace F, ∑ i, w (b i), by positivity, fun t => ?_⟩
  have hopen : IsOpen {y : InfiniteAdeleRing F | ∀ w, ‖y w - t w‖ < 1} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (((continuous_apply w : Continuous fun y : InfiniteAdeleRing F => y w).sub
        continuous_const).norm) continuous_const
  obtain ⟨f, hf⟩ := (InfiniteAdeleRing.denseRange_algebraMap F).exists_mem_open hopen
    ⟨t, fun w => by
      show ‖t w - t w‖ < 1
      rw [sub_self, norm_zero]; exact one_pos⟩
  have hf' : ∀ w, ‖algebraMap F w.Completion f - t w‖ < 1 := hf
  refine ⟨∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i, fun w => ?_⟩
  have e : ((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f =
      ∑ i, (((⌊b.repr f i⌋ : ℚ) - b.repr f i : ℚ) : F) * b i := by
    conv_lhs => arg 2; rw [← b.sum_repr f]
    rw [show ((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) =
      algebraMap (𝓞 F) F (∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i) from rfl, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← integralBasis_apply, ← hb, Rat.smul_def, zsmul_eq_mul]
    push_cast
    ring
  have h2 : ‖algebraMap F w.Completion (((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f)‖ ≤
      ∑ i, w (b i) := by
    rw [e, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_alg_inf, map_mul]
    refine mul_le_of_le_one_left (apply_nonneg _ _) ?_
    rw [← InfinitePlace.norm_embedding_eq, map_ratCast, Complex.norm_ratCast, ← Rat.cast_abs, ← Rat.cast_one, Rat.cast_le,
      abs_le]
    constructor <;> linarith [Int.floor_le (b.repr f i), Int.lt_floor_add_one (b.repr f i)]
  have h3 : ∑ i, w (b i) ≤ ∑ w : InfinitePlace F, ∑ i, w (b i) :=
    Finset.single_le_sum (f := fun w : InfinitePlace F => ∑ i, w (b i))
      (fun _ _ => Finset.sum_nonneg fun _ _ => apply_nonneg _ _) (Finset.mem_univ w)
  have h4 := norm_add_le (algebraMap F w.Completion (((∑ i, ⌊b.repr f i⌋ • RingOfIntegers.basis F i : 𝓞 F) : F) - f))
    (algebraMap F w.Completion f - t w)
  rw [map_sub, sub_add_sub_cancel, ← map_sub] at h4
  linarith [hf' w]

open NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal Module in
open scoped nonZeroDivisors in

theorem exists_small_elt (v₀ : HeightOneSpectrum (𝓞 F)) (η : ℝ) (hη : 0 < η) :
    ∃ x : F, x ≠ 0 ∧ (∀ w : InfinitePlace F, w x < η) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → ‖algebraMap F (v.adicCompletion F) x‖ ≤ 1 := by
  classical
  let f : InfinitePlace F → NNReal := fun _ => ⟨η, hη.le⟩
  have hV : volume (convexBodyLT F f) ≠ ⊤ := by
    rw [convexBodyLT_volume]; exact mul_ne_top coe_ne_top coe_ne_top
  have hV0 : 0 < (volume (convexBodyLT F f)).toReal := by
    rw [convexBodyLT_volume, toReal_mul, coe_toReal, coe_toReal]
    have h1 : (1 : ℝ) ≤ convexBodyLTFactor F := by exact_mod_cast one_le_convexBodyLTFactor F
    refine mul_pos (by linarith) ?_
    rw [NNReal.coe_prod]
    exact Finset.prod_pos fun w _ => by rw [NNReal.coe_pow]; exact pow_pos hη _
  set B : ℝ := (volume (ZSpan.fundamentalDomain (latticeBasis F))).toReal * 2 ^ finrank ℝ (mixedSpace F) with hB
  have hq : (1 : ℝ) < Ideal.absNorm v₀.asIdeal := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v₀
  have ht : Tendsto (fun k : ℕ => ((Ideal.absNorm v₀.asIdeal : ℝ)⁻¹) ^ k * B) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (Ideal.absNorm v₀.asIdeal : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hq)).mul_const B
    rwa [zero_mul] at this
  obtain ⟨k, hk⟩ := (ht.eventually (Iio_mem_nhds hV0)).exists
  have hI : ((v₀.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero k v₀.ne_bot)
  let J : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 _ (inv_ne_zero hI)
  have h : minkowskiBound F J < volume (convexBodyLT F f) := by
    rw [← ENNReal.toReal_lt_toReal (minkowskiBound_lt_top F J).ne hV]
    refine lt_of_eq_of_lt ?_ hk
    rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis, toReal_mul, toReal_mul, toReal_pow,
      ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)), hB]
    simp only [J, Units.val_mk0, map_inv₀, FractionalIdeal.coeIdeal_absNorm, map_pow, toReal_ofNat]
    push_cast
    rw [inv_pow]
    ring
  obtain ⟨a, ha, hne, hlt⟩ := exists_ne_zero_mem_ideal_lt F J h
  refine ⟨a, hne, fun w => hlt w, fun v hv => ?_⟩
  obtain ⟨p, hp0, hpv⟩ : ∃ p ∈ v₀.asIdeal, p ∉ v.asIdeal := by
    by_contra hc
    push Not at hc
    exact hv (HeightOneSpectrum.ext (v₀.isMaximal.eq_of_le v.isPrime.ne_top hc).symm)
  have hm : a * algebraMap (𝓞 F) F (p ^ k) ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← inv_mul_cancel₀ hI]
    exact FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.pow_mem_pow hp0 k))
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hm
  have h1 := norm_int_le_one v o
  rw [show (o : F) = algebraMap (𝓞 F) F o from rfl, ho, map_mul, norm_mul, map_pow, map_pow, norm_pow] at h1
  have h2 := norm_int_eq_one v p hpv
  rw [show (p : F) = algebraMap (𝓞 F) F p from rfl] at h2
  rwa [h2, one_pow, mul_one] at h1

theorem strong_approx (v₀ : HeightOneSpectrum (𝓞 F)) (t : InfiniteAdeleRing F) (s : FiniteAdeleRing (𝓞 F) F)
    (M : ℕ) (hM : M ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : F, c ≠ 0 ∧ (∀ w : InfinitePlace F, ‖algebraMap F w.Completion c - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) c - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hMR : (0 : ℝ) < M := Nat.cast_pos.2 (Nat.pos_of_ne_zero hM)
  obtain ⟨u, hu⟩ := PI.UnipApproxD.IntegersDenseFiniteAdeles.exists_approx_adele
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (M : F)⁻¹ * s)
  obtain ⟨C, hC, hCt⟩ := exists_int_near F
  obtain ⟨x, hx0, hxw, hxv⟩ := exists_small_elt v₀ (ε / (M * (C + 1))) (by positivity)
  obtain ⟨o, ho⟩ := hCt fun w => (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)
  have key : ∀ o' : 𝓞 F, (∀ w : InfinitePlace F, ‖algebraMap F w.Completion (o' : F) -
      (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)‖ < C + 1) →
      (∀ w : InfinitePlace F, ‖algebraMap F w.Completion (M * u + M * x * o') - t w‖ < ε) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        ‖algebraMap F (v.adicCompletion F) (M * u + M * x * o') - s v‖ ≤ ‖(M : v.adicCompletion F)‖ := by
    intro o' ho'
    refine ⟨fun w => ?_, fun v hv => ?_⟩
    · have h0 : algebraMap F w.Completion (M * x) ≠ 0 := (map_ne_zero _).2 (mul_ne_zero hMF hx0)
      have e : algebraMap F w.Completion (M * u + M * x * o') - t w = algebraMap F w.Completion (M * x) *
          (algebraMap F w.Completion (o' : F) -
            (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x)) := by
        rw [map_add, map_mul _ (M * x), mul_sub, mul_div_cancel₀ _ h0]; ring
      rw [e, norm_mul, norm_alg_inf, map_mul, InfinitePlace.map_natCast]
      calc _ ≤ (M * w x) * (C + 1) := mul_le_mul_of_nonneg_left (ho' w).le (by positivity)
        _ < (M * (ε / (M * (C + 1)))) * (C + 1) := by gcongr; exact hxw w
        _ = ε := by field_simp
    · have h0 := nat_ne_zero_fin v hM
      have hu' : ‖algebraMap F (v.adicCompletion F) (M : F)⁻¹ * s v - algebraMap F (v.adicCompletion F) u‖ ≤ 1 :=
        (norm_le_one_iff_int v _).2 (hu v)
      have e : algebraMap F (v.adicCompletion F) (M * u + M * x * o') - s v = (M : v.adicCompletion F) *
          (-(algebraMap F (v.adicCompletion F) (M : F)⁻¹ * s v - algebraMap F (v.adicCompletion F) u) +
            algebraMap F (v.adicCompletion F) x * algebraMap F (v.adicCompletion F) (o' : F)) := by
        simp only [map_add, map_mul, map_inv₀, map_natCast]
        field_simp
        ring
      rw [e, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))
      · rwa [norm_neg]
      · rw [norm_mul]; exact mul_le_one₀ (hxv v hv) (norm_nonneg _) (norm_int_le_one v o')
  by_cases hc : (M : F) * u + M * x * o = 0
  · refine ⟨M * u + M * x * (o + 1 : 𝓞 F), ?_, key (o + 1) fun w => ?_⟩
    · have : (M : F) * u + M * x * (o + 1 : 𝓞 F) = M * x := by push_cast; linear_combination hc
      rw [this]; exact mul_ne_zero hMF hx0
    · have h1 := norm_add_le (1 : w.Completion) (algebraMap F w.Completion (o : F) -
        (t w - algebraMap F w.Completion (M * u)) / algebraMap F w.Completion (M * x))
      have e : ((o + 1 : 𝓞 F) : F) = 1 + o := by push_cast; ring
      rw [e, map_add, map_one, add_sub_assoc]
      rw [norm_one] at h1
      linarith [ho w]
  · exact ⟨_, hc, key o fun w => (ho w).trans (lt_add_one C)⟩

end GlobalTheory.HeckeSplitAll.Approx

end

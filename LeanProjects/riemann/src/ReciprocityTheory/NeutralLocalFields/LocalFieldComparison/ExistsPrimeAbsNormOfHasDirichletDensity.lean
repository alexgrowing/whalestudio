import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TendstoPrimeIdealZetaSumUniv

noncomputable section

namespace ReciprocityTheory.Neutral.Bridge

open NumberField IsDedekindDomain Filter Topology

variable {K : Type*} [Field K] [NumberField K]

def ratPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) : ℕ := Ideal.absNorm (𝔭.asIdeal.under ℤ)

private theorem under_int_isMaximal (𝔭 : HeightOneSpectrum (𝓞 K)) : (𝔭.asIdeal.under ℤ).IsMaximal := by
  have := 𝔭.isMaximal
  exact Ideal.IsMaximal.under ℤ 𝔭.asIdeal

private theorem under_int_ne_bot' (𝔭 : HeightOneSpectrum (𝓞 K)) : 𝔭.asIdeal.under ℤ ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField (under_int_isMaximal 𝔭) Int.not_isField

private theorem int_ideal_eq_span_absNorm (J : Ideal ℤ) : J = Ideal.span {((Ideal.absNorm J : ℕ) : ℤ)} := by
  obtain ⟨a, rfl⟩ : ∃ a, J = Ideal.span {a} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator J).symm⟩
  rw [Ideal.absNorm_span_singleton]
  simp [Algebra.norm_self]

private theorem under_eq_span_ratPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    𝔭.asIdeal.under ℤ = Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : ℤ)} :=
  int_ideal_eq_span_absNorm _

theorem ratPrimeBelow_prime (𝔭 : HeightOneSpectrum (𝓞 K)) : (ratPrimeBelow 𝔭).Prime := by
  have hprime : (Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : ℤ)}).IsPrime := by
    rw [← under_eq_span_ratPrimeBelow 𝔭]; exact (under_int_isMaximal 𝔭).isPrime
  have h0 : ((ratPrimeBelow 𝔭 : ℕ) : ℤ) ≠ 0 := by
    intro h
    apply under_int_ne_bot' 𝔭
    rw [under_eq_span_ratPrimeBelow 𝔭, h]
    exact Ideal.span_singleton_eq_bot.2 rfl
  rw [Nat.prime_iff_prime_int]
  exact (Ideal.span_singleton_prime h0).1 hprime

private theorem natCast_ratPrimeBelow_mem (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ((ratPrimeBelow 𝔭 : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal := by
  have h1 : ((ratPrimeBelow 𝔭 : ℕ) : ℤ) ∈ 𝔭.asIdeal.under ℤ := by
    rw [under_eq_span_ratPrimeBelow 𝔭]; exact Ideal.subset_span rfl
  have h2 : algebraMap ℤ (𝓞 K) ((ratPrimeBelow 𝔭 : ℕ) : ℤ) ∈ 𝔭.asIdeal := h1
  simpa using h2

private theorem absNorm_span_natCast_eq_pow_finrank (p : ℕ) :
    Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton]
  have : ((p : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((p : ℕ) : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
  simp [Int.natAbs_pow]

theorem absNorm_eq_ratPrimeBelow_pow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    ∃ f : ℕ, Ideal.absNorm 𝔭.asIdeal = ratPrimeBelow 𝔭 ^ f := by
  have hp := ratPrimeBelow_prime 𝔭
  have hle : Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : 𝓞 K)} ≤ 𝔭.asIdeal :=
    Ideal.span_le.2 (Set.singleton_subset_iff.2 (natCast_ratPrimeBelow_mem 𝔭))
  have hdvd : Ideal.absNorm 𝔭.asIdeal ∣ Ideal.absNorm (Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : 𝓞 K)}) := by
    exact Ideal.absNorm_dvd_absNorm_of_le hle
  rw [absNorm_span_natCast_eq_pow_finrank] at hdvd
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact ⟨f, hf⟩

theorem ratPrimeBelow_sq_le (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ (Ideal.absNorm 𝔭.asIdeal).Prime) :
    ratPrimeBelow 𝔭 ^ 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
  obtain ⟨f, hf⟩ := absNorm_eq_ratPrimeBelow_pow 𝔭
  have hp := ratPrimeBelow_prime 𝔭
  have h2 : 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
    exact_mod_cast ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.two_le_absNorm (K := K) 𝔭
  rw [hf] at h h2 ⊢
  rcases f with _ | _ | f
  · simp at h2
  · exact (h (by simpa using hp)).elim
  · exact Nat.pow_le_pow_right hp.pos (by omega)

theorem mem_primesOverFinset_ratPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    𝔭.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : ℤ)}) (𝓞 K) := by
  rw [← under_eq_span_ratPrimeBelow 𝔭]
  have := under_int_isMaximal 𝔭
  have := 𝔭.isMaximal
  have : 𝔭.asIdeal.IsPrime := 𝔭.isPrime
  rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset (under_int_ne_bot' 𝔭)]
  exact ⟨inferInstance, ⟨rfl⟩⟩

private theorem span_natCast_isMaximal_of_prime (p : ℕ) (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal := by
  exact PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible

theorem card_primesOverFinset_span_le_finrank (p : ℕ) (hp : p.Prime) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)).card ≤ Module.finrank ℚ K := by
  have := span_natCast_isMaximal_of_prime p hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  have hsum := Ideal.sum_ramification_inertia (p := Ideal.span {(p : ℤ)}) (S := 𝓞 K) ℚ K hp0
  rw [← hsum, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro P hP
  rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hp0] at hP
  obtain ⟨hPp, hPo⟩ := hP
  have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ P := by
    exact Ideal.map_le_of_le_comap (le_of_eq hPo.over)
  have he : (Ideal.span {(p : ℤ)}).ramificationIdx' P ≠ 0 := by
    exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero (Ideal.map_ne_bot_of_ne_bot hp0) hPp hle
  have hf : (Ideal.span {(p : ℤ)}).inertiaDeg' P ≠ 0 := by
    exact (Ideal.inertiaDeg'_pos (Ideal.span {(p : ℤ)}) P).ne'
  exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero he hf)

theorem card_fiber_ratPrimeBelow_le {ι : Type*} (g : ι → HeightOneSpectrum (𝓞 K)) (hg : Function.Injective g)
    (F : Finset ι) (p : ℕ) (hp : p.Prime) :
    (F.filter fun x => ratPrimeBelow (g x) = p).card ≤ Module.finrank ℚ K := by
  calc (F.filter fun x => ratPrimeBelow (g x) = p).card
      ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 K)).card := by
        apply Finset.card_le_card_of_injOn (fun x => (g x).asIdeal)
        · intro x hx
          have hx' : x ∈ F.filter (fun x => ratPrimeBelow (g x) = p) := hx
          have h2 := (Finset.mem_filter.1 hx').2
          have h3 := mem_primesOverFinset_ratPrimeBelow (g x)
          rw [h2] at h3
          exact h3
        · intro x _ y _ hxy
          exact hg (HeightOneSpectrum.ext hxy)
    _ ≤ _ := card_primesOverFinset_span_le_finrank (K := K) p hp

theorem rpow_neg_le_inv_ratPrimeBelow_sq (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ (Ideal.absNorm 𝔭.asIdeal).Prime)
    {s : ℝ} (hs : 1 < s) :
    (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 1 / (ratPrimeBelow 𝔭 : ℝ) ^ 2 := by
  have hp := ratPrimeBelow_prime 𝔭
  have hsq : ((ratPrimeBelow 𝔭 : ℝ)) ^ 2 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
    exact_mod_cast ratPrimeBelow_sq_le 𝔭 h
  have hpos : (0:ℝ) < (ratPrimeBelow 𝔭 : ℝ) ^ 2 := by
    have := hp.pos; positivity
  have h2 := ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.two_le_absNorm (K := K) 𝔭
  calc (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = 1 / (Ideal.absNorm 𝔭.asIdeal : ℝ) := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / (ratPrimeBelow 𝔭 : ℝ) ^ 2 := one_div_le_one_div_of_le hpos hsq

private theorem sum_absNorm_rpow_neg_le_of_not_prime {ι : Type*} (g : ι → HeightOneSpectrum (𝓞 K))
    (hg : Function.Injective g) (U : Finset ι)
    (hU : ∀ x ∈ U, ¬ (Ideal.absNorm (g x).asIdeal).Prime) {s : ℝ} (hs : 1 < s) :
    ∑ x ∈ U, (Ideal.absNorm (g x).asIdeal : ℝ) ^ (-s) ≤
      (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, 1 / (m : ℝ) ^ 2 := by
  have hsum : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  calc ∑ x ∈ U, (Ideal.absNorm (g x).asIdeal : ℝ) ^ (-s)
      ≤ ∑ x ∈ U, 1 / (ratPrimeBelow (g x) : ℝ) ^ 2 :=
        Finset.sum_le_sum fun x hx => rpow_neg_le_inv_ratPrimeBelow_sq _ (hU x hx) hs
    _ = ∑ m ∈ U.image (fun x => ratPrimeBelow (g x)),
          ∑ x ∈ U.filter (fun x => ratPrimeBelow (g x) = m), 1 / (ratPrimeBelow (g x) : ℝ) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem _ hx) _).symm
    _ = ∑ m ∈ U.image (fun x => ratPrimeBelow (g x)),
          ((U.filter (fun x => ratPrimeBelow (g x) = m)).card : ℝ) * (1 / (m : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_congr rfl (g := fun _ => 1 / (m : ℝ) ^ 2)
          (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ m ∈ U.image (fun x => ratPrimeBelow (g x)), (Module.finrank ℚ K : ℝ) * (1 / (m : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun m hm => ?_
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hm
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast card_fiber_ratPrimeBelow_le g hg U _ (ratPrimeBelow_prime _)
    _ = (Module.finrank ℚ K : ℝ) * ∑ m ∈ U.image (fun x => ratPrimeBelow (g x)), 1 / (m : ℝ) ^ 2 :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, 1 / (m : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact hsum.sum_le_tsum _ (fun m _ => by positivity)

theorem exists_bound_primeIdealZetaSum_not_prime :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s →
      NumberField.Set.primeIdealZetaSum {𝔭 : HeightOneSpectrum (𝓞 K) | ¬ (Ideal.absNorm 𝔭.asIdeal).Prime} s ≤ C := by
  refine ⟨(Module.finrank ℚ K : ℝ) * ∑' m : ℕ, 1 / (m : ℝ) ^ 2, fun s hs => ?_⟩
  unfold NumberField.Set.primeIdealZetaSum
  refine tsum_le_of_sum_le' (mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg fun m => by positivity))
    fun U => ?_
  exact sum_absNorm_rpow_neg_le_of_not_prime Subtype.val Subtype.val_injective U (fun x _ => x.2) hs

theorem exists_prime_absNorm_of_hasDirichletDensity {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : NumberField.Set.HasDirichletDensity S δ) (hδ : 0 < δ) {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) :
    ∃ 𝔭 ∈ S, 𝔭 ∉ T ∧ (Ideal.absNorm 𝔭.asIdeal).Prime := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨B, hB0, hbound⟩ : ∃ B : ℝ, 0 ≤ B ∧
      ∀ s : ℝ, 1 < s → NumberField.Set.primeIdealZetaSum S s ≤ B := by
    refine ⟨(hT.toFinset.card : ℝ) + (Module.finrank ℚ K : ℝ) * ∑' m : ℕ, 1 / (m : ℝ) ^ 2,
      add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
        (tsum_nonneg fun m => by positivity)), fun s hs => ?_⟩
    unfold NumberField.Set.primeIdealZetaSum
    refine tsum_le_of_sum_le' (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
        (tsum_nonneg fun m => by positivity))) fun U => ?_
    rw [← Finset.sum_filter_add_sum_filter_not U
      (fun x : S => (x : HeightOneSpectrum (𝓞 K)) ∈ T)]
    refine add_le_add ?_ ?_
    · calc ∑ x ∈ U.filter (fun x : S => (x : HeightOneSpectrum (𝓞 K)) ∈ T),
            (Ideal.absNorm (x : HeightOneSpectrum (𝓞 K)).asIdeal : ℝ) ^ (-s)
          ≤ ∑ x ∈ U.filter (fun x : S => (x : HeightOneSpectrum (𝓞 K)) ∈ T), (1 : ℝ) := by
            refine Finset.sum_le_sum fun x _ => Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
            have := ReciprocityTheory.Neutral.Bridge.DedekindZetaReal.two_le_absNorm (K := K) (x : HeightOneSpectrum (𝓞 K))
            linarith
        _ = ((U.filter (fun x : S => (x : HeightOneSpectrum (𝓞 K)) ∈ T)).card : ℝ) := by simp
        _ ≤ (hT.toFinset.card : ℝ) := by
            refine Nat.cast_le.2 (Finset.card_le_card_of_injOn Subtype.val ?_
              Subtype.val_injective.injOn)
            intro x hx
            have hx' := (Finset.mem_filter.1 hx).2
            exact (Set.Finite.mem_toFinset hT).2 hx'
    · refine sum_absNorm_rpow_neg_le_of_not_prime (ι := S) Subtype.val Subtype.val_injective _ ?_ hs
      intro x hx
      exact hcon x.1 x.2 (Finset.mem_filter.1 hx).2
  have h' : Tendsto (fun s => NumberField.Set.primeIdealZetaSum S s /
      NumberField.Set.primeIdealZetaSum Set.univ s) (𝓝[>] 1) (𝓝 δ) := h
  have hU := tendsto_primeIdealZetaSum_univ (K := K)
  have h1 : ∀ᶠ s in 𝓝[>] (1 : ℝ), δ / 2 < NumberField.Set.primeIdealZetaSum S s /
      NumberField.Set.primeIdealZetaSum Set.univ s :=
    h'.eventually (lt_mem_nhds (show δ / 2 < δ by linarith))
  have h2 : ∀ᶠ s in 𝓝[>] (1 : ℝ), 2 * (B + 1) / δ <
      NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s :=
    hU.eventually (eventually_gt_atTop (2 * (B + 1) / δ))
  have h3 : ∀ᶠ s in 𝓝[>] (1 : ℝ), s ∈ Set.Ioi (1 : ℝ) := self_mem_nhdsWithin
  obtain ⟨s, hs1, hs2, hs3⟩ := (h1.and (h2.and h3)).exists
  have hc : 0 < 2 * (B + 1) / δ := div_pos (by linarith) hδ
  have hpos : 0 < NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s := lt_trans hc hs2
  have hS := hbound s hs3
  have h4 : δ / 2 * NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s < NumberField.Set.primeIdealZetaSum S s := by
    exact (lt_div_iff₀ hpos).1 hs1
  have h5 : δ / 2 * (2 * (B + 1) / δ) < δ / 2 * NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) s :=
    mul_lt_mul_of_pos_left hs2 (by linarith)
  have h6 : δ / 2 * (2 * (B + 1) / δ) = B + 1 := by
    have hδ' : δ ≠ 0 := hδ.ne'
    field_simp
    try ring
  rw [h6] at h5
  linarith

end ReciprocityTheory.Neutral.Bridge

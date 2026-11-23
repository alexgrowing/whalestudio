import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.Desc.IT

section Gen

variable {K : Type} [Field K] [NumberField K]

lemma exists_prime_mem (P : HeightOneSpectrum (𝓞 K)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ P.asIdeal := by
  have hn : Ideal.absNorm P.asIdeal ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff] at h
    exact P.ne_bot h
  have hmem := Ideal.absNorm_mem P.asIdeal
  rw [← Nat.prod_primeFactorsList hn, Nat.cast_list_prod, ← Multiset.prod_coe] at hmem
  obtain ⟨x, hx, hxP⟩ := (P.isPrime.multiset_prod_mem_iff_exists_mem _).mp hmem
  rw [Multiset.mem_coe, List.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨q, Nat.prime_of_mem_primeFactorsList hq, hxP⟩

lemma span_max {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsMaximal := by
  haveI := Fact.mk hp
  exact Int.ideal_span_isMaximal_of_prime p

lemma span_eq (P : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime) (hm : (p : 𝓞 K) ∈ P.asIdeal) :
    Ideal.span {(p : ℤ)} = P.asIdeal.comap (algebraMap ℤ (𝓞 K)) := by
  apply (span_max hp).eq_of_le
  · exact Ideal.comap_ne_top _ P.isPrime.ne_top
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    simpa using hm

lemma liesOver_of_mem (P : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime) (hm : (p : 𝓞 K) ∈ P.asIdeal) :
    P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨span_eq P hp hm⟩

lemma absNorm_pow (P : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime) (hm : (p : 𝓞 K) ∈ P.asIdeal) :
    ∃ f, 1 ≤ f ∧ Ideal.absNorm P.asIdeal = p ^ f := by
  haveI := liesOver_of_mem P hp hm
  have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P.asIdeal hp
  refine ⟨_, ?_, h1⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at h1
  exact P.isPrime.ne_top h1

open scoped Classical in
lemma card_le {p : ℕ} (hp : p.Prime) (s : Finset (HeightOneSpectrum (𝓞 K))) :
    (s.filter fun P => (p : 𝓞 K) ∈ P.asIdeal).card ≤ Module.finrank ℚ K := by
  set pZ : Ideal ℤ := Ideal.span {(p : ℤ)} with hpZ
  haveI : pZ.IsMaximal := span_max hp
  haveI : Fintype (pZ.primesOver (𝓞 K)) :=
    (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 K) pZ).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank pZ (𝓞 K)
  have hsub : (s.filter fun P => (p : 𝓞 K) ∈ P.asIdeal).image (fun P => P.asIdeal) ⊆
      (Finset.univ : Finset (pZ.primesOver (𝓞 K))).map
        ⟨Subtype.val, Subtype.val_injective⟩ := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    rw [Finset.mem_filter] at hP
    rw [Finset.mem_map]
    exact ⟨⟨P.asIdeal, P.isPrime, liesOver_of_mem P hp hP.2⟩, Finset.mem_univ _, rfl⟩
  calc (s.filter fun P => (p : 𝓞 K) ∈ P.asIdeal).card
      = ((s.filter fun P => (p : 𝓞 K) ∈ P.asIdeal).image (fun P => P.asIdeal)).card :=
        (Finset.card_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)).symm
    _ ≤ ((Finset.univ : Finset (pZ.primesOver (𝓞 K))).map
        ⟨Subtype.val, Subtype.val_injective⟩).card := Finset.card_le_card hsub
    _ = ∑ _q : pZ.primesOver (𝓞 K), 1 := by simp
    _ ≤ ∑ q : pZ.primesOver (𝓞 K), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
        apply Finset.sum_le_sum
        intro q _
        haveI := q.2.1
        exact Nat.mul_pos (Ideal.ramificationIdx_pos q.1 ℤ) (Ideal.inertiaDeg_pos q.1 ℤ)
    _ = Module.finrank ℤ (𝓞 K) := hsum
    _ = Module.finrank ℚ K := RingOfIntegers.rank K

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma key (w : HeightOneSpectrum (𝓞 E)) (hns : ¬ IsSplitAt w)
    (hT : ¬ w.asIdeal ∣ differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (hm : (p : 𝓞 E) ∈ w.asIdeal) : p ^ 2 ≤ Ideal.absNorm w.asIdeal := by
  set F := maximalRealSubfield E
  set v : HeightOneSpectrum (𝓞 F) := w.under (𝓞 F) with hvdef
  haveI hvw : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by
    rw [Ideal.over_def w.asIdeal v.asIdeal, Ideal.under, Ideal.mem_comap, map_natCast]
    exact hm
  obtain ⟨f0, hf0, hv⟩ := absNorm_pow v hp hpv
  have hnorm := Ideal.absNorm_pow_inertiaDeg (R := 𝓞 F) v.asIdeal w.asIdeal
  suffices hf : 2 ≤ w.asIdeal.inertiaDeg (𝓞 F) by
    rw [← hnorm, hv, ← pow_mul]
    calc p ^ 2 ≤ p ^ (f0 * 2) := Nat.pow_le_pow_right hp.pos (by omega)
      _ ≤ p ^ (f0 * w.asIdeal.inertiaDeg (𝓞 F)) :=
        Nat.pow_le_pow_right hp.pos (Nat.mul_le_mul_left _ hf)
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  haveI : Fintype (v.asIdeal.primesOver (𝓞 E)) :=
    (Algebra.QuasiFinite.finite_primesOver (S := 𝓞 E) v.asIdeal).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)
  have hrank : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F E
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  have huniq : ∀ q : v.asIdeal.primesOver (𝓞 E), q.1 = w.asIdeal := by
    intro q
    obtain ⟨hqp, hql⟩ := q.2
    have hq0 : q.1 ≠ ⊥ := by
      intro h
      apply v.ne_bot
      rw [Ideal.over_def q.1 v.asIdeal, h, Ideal.under, Ideal.comap_bot_of_injective _ hinj]
    by_contra hne
    apply hns
    refine ⟨⟨q.1, hqp, hq0⟩, ?_, ?_⟩
    · intro h
      apply hne
      rw [← h]
    · apply HeightOneSpectrum.ext
      show q.1.under (𝓞 F) = w.asIdeal.under (𝓞 F)
      rw [← Ideal.over_def q.1 v.asIdeal, ← Ideal.over_def w.asIdeal v.asIdeal]
  let q0 : v.asIdeal.primesOver (𝓞 E) := ⟨w.asIdeal, w.isPrime, hvw⟩
  rw [Fintype.sum_eq_single q0 (fun q hq => absurd (Subtype.ext (huniq q)) hq), hrank] at hsum
  by_contra hlt
  push_neg at hlt
  have hfpos := Ideal.inertiaDeg_pos w.asIdeal (𝓞 F)
  have hf1 : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by omega
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 2 := by
    have := hsum
    simp only [q0] at this
    rw [hf1, mul_one] at this
    exact this
  have he' : v.asIdeal.ramificationIdx' w.asIdeal = 2 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot, he]
  have hdvd : w.asIdeal ^ 2 ∣ v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [Ideal.dvd_iff_le, ← he']
    exact Ideal.le_pow_ramificationIdx'
  have := pow_sub_one_dvd_differentIdeal (𝓞 F) w.asIdeal 2 v.ne_bot hdvd
  rw [show 2 - 1 = 1 from rfl, pow_one] at this
  exact hT this

end CM

end PositivityTheory.Rg.BcB.Desc.IT

namespace PositivityTheory.Rg.BcB.Desc

open IT in
theorem inertThin_holds : InertThin := by
  intro E _ _ _
  classical
  set D := differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) with hDdef
  have hD : D ≠ ⊥ := differentIdeal_ne_bot
  have hfin := Ideal.finite_factors hD
  set Ram := hfin.toFinset with hRam
  choose g hg using fun w : HeightOneSpectrum (𝓞 E) => exists_prime_mem w
  have hS : Summable fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hne : ∀ w : HeightOneSpectrum (𝓞 E), Ideal.absNorm w.asIdeal ≠ 0 := fun w h =>
    w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  refine summable_of_sum_le (c := (Ram.card : ℝ) +
    (Module.finrank ℚ E : ℝ) * ∑' k : ℕ, (1 : ℝ) / (k : ℝ) ^ 2) (fun w => by positivity) ?_
  intro u
  rw [← Finset.sum_filter_add_sum_filter_not u (fun w => w.1 ∈ Ram)]
  apply add_le_add
  · have hcard : (u.filter (fun w => w.1 ∈ Ram)).card ≤ Ram.card := by
      apply Finset.card_le_card_of_injOn
        (fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ IsSplitAt w} => w.1)
      · intro w hw
        rw [Finset.mem_coe, Finset.mem_filter] at hw
        exact hw.2
      · intro a _ b _ h
        exact Subtype.ext h
    calc ∑ w ∈ u.filter (fun w => w.1 ∈ Ram), ((Ideal.absNorm w.1.asIdeal : ℝ))⁻¹
        ≤ ∑ w ∈ u.filter (fun w => w.1 ∈ Ram), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro w _
          apply inv_le_one_of_one_le₀
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hne w.1)
      _ = ((u.filter (fun w => w.1 ∈ Ram)).card : ℝ) := by simp
      _ ≤ (Ram.card : ℝ) := by exact_mod_cast hcard
  · set u' := u.filter (fun w => w.1 ∉ Ram) with hu'
    have hkey : ∀ w ∈ u', ((Ideal.absNorm w.1.asIdeal : ℝ))⁻¹ ≤ 1 / (g w.1 : ℝ) ^ 2 := by
      intro w hw
      have hnot : w.1 ∉ Ram := (Finset.mem_filter.mp hw).2
      have hnd : ¬ w.1.asIdeal ∣ D := by
        intro h
        apply hnot
        rw [hRam, Set.Finite.mem_toFinset]
        exact h
      have h2 := key w.1 w.2 hnd (hg w.1).1 (hg w.1).2
      have hgpos : (0 : ℝ) < (g w.1 : ℝ) ^ 2 := by
        have := (hg w.1).1.pos
        positivity
      rw [one_div]
      apply inv_anti₀ hgpos
      exact_mod_cast h2
    have hfib : ∀ k ∈ u'.image (fun w => g w.1),
        ((u'.filter (fun w => g w.1 = k)).card : ℝ) ≤ (Module.finrank ℚ E : ℝ) := by
      intro k hk
      obtain ⟨w0, _, hw0⟩ := Finset.mem_image.mp hk
      have hkp : k.Prime := hw0 ▸ (hg w0).1
      have hc := card_le (K := E) hkp (u'.image (fun w => w.1))
      have hle : (u'.filter (fun w => g w.1 = k)).card ≤
          ((u'.image (fun w => w.1)).filter fun P => (k : 𝓞 E) ∈ P.asIdeal).card := by
        apply Finset.card_le_card_of_injOn
          (fun w : {w : HeightOneSpectrum (𝓞 E) // ¬ IsSplitAt w} => w.1)
        · intro w hw
          rw [Finset.mem_coe, Finset.mem_filter] at hw
          rw [Finset.mem_coe, Finset.mem_filter]
          refine ⟨Finset.mem_image_of_mem _ hw.1, ?_⟩
          rw [← hw.2]
          exact (hg w.1).2
        · intro a _ b _ h
          exact Subtype.ext h
      exact_mod_cast hle.trans hc
    calc ∑ w ∈ u', ((Ideal.absNorm w.1.asIdeal : ℝ))⁻¹
        ≤ ∑ w ∈ u', 1 / (g w.1 : ℝ) ^ 2 := Finset.sum_le_sum hkey
      _ = ∑ k ∈ u'.image (fun w => g w.1),
            ∑ w ∈ u'.filter (fun w => g w.1 = k), 1 / (g w.1 : ℝ) ^ 2 :=
          (Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem _ hw) _).symm
      _ = ∑ k ∈ u'.image (fun w => g w.1),
            ((u'.filter (fun w => g w.1 = k)).card : ℝ) * (1 / (k : ℝ) ^ 2) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2])]
          simp
      _ ≤ ∑ k ∈ u'.image (fun w => g w.1), (Module.finrank ℚ E : ℝ) * (1 / (k : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_right (hfib k hk) (by positivity)
      _ = (Module.finrank ℚ E : ℝ) * ∑ k ∈ u'.image (fun w => g w.1), 1 / (k : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (Module.finrank ℚ E : ℝ) * ∑' k : ℕ, (1 : ℝ) / (k : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hS.sum_le_tsum _ (fun k _ => by positivity)

end PositivityTheory.Rg.BcB.Desc

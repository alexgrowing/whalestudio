import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive

open IsLocalRing

namespace GlobalTheory.PurFree

theorem span_succAbove_eq_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {k : ℕ}
    (e : Fin (k + 1) → M) (he : Submodule.span R (Set.range e) = ⊤) (a : Fin (k + 1) → R)
    (ha : ∑ i, a i • e i = 0) (j : Fin (k + 1)) (hj : IsUnit (a j)) :
    Submodule.span R (Set.range (e ∘ j.succAbove)) = ⊤ := by
  set N := Submodule.span R (Set.range (e ∘ j.succAbove))
  have hsa : ∀ i : Fin k, e (j.succAbove i) ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hej : e j ∈ N := by
    rw [Fin.sum_univ_succAbove _ j] at ha
    obtain ⟨u, hu⟩ := hj
    have h1 := eq_neg_of_add_eq_zero_left ha
    have : e j = -(↑u⁻¹ : R) • ∑ i : Fin k, a (j.succAbove i) • e (j.succAbove i) := by
      calc e j = ((↑u⁻¹ : R) * a j) • e j := by rw [← hu, Units.inv_mul, one_smul]
        _ = (↑u⁻¹ : R) • (a j • e j) := mul_smul _ _ _
        _ = _ := by rw [h1, smul_neg, neg_smul]
    rw [this]
    exact N.smul_mem _ (N.sum_mem fun i _ => N.smul_mem _ (hsa i))
  rw [eq_top_iff, ← he, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rcases Fin.eq_self_or_eq_succAbove j i with h | ⟨i', rfl⟩
  · rw [h]; exact hej
  · exact hsa i'

theorem exists_span_fin_pred {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ)
    (e : Fin n → M) (he : Submodule.span R (Set.range e) = ⊤) (a : Fin n → R)
    (ha : ∑ i, a i • e i = 0) (j : Fin n) (hj : IsUnit (a j)) :
    ∃ e' : Fin (n - 1) → M, Submodule.span R (Set.range e') = ⊤ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := j.pos; omega⟩
  exact ⟨e ∘ j.succAbove, span_succAbove_eq_top e he a ha j hj⟩

theorem free_of_relations {R M : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (x y : R)
    (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
    (hrel : ∀ (n : ℕ) (e : Fin n → M), Submodule.span R (Set.range e) = ⊤ →
      ∀ a : Fin n → R, ∑ i, a i • e i = 0 → (∀ i, a i ∈ maximalIdeal R) →
      ∃ b c : Fin n → R, ∑ i, b i • e i = 0 ∧ ∑ i, c i • e i = 0 ∧ a = x • b + y • c) :
    Module.Free R M := by
  classical
  have hex : ∃ n, ∃ e : Fin n → M, Submodule.span R (Set.range e) = ⊤ := Module.Finite.exists_fin
  obtain ⟨e, he⟩ := Nat.find_spec hex
  have hmin : ∀ a : Fin (Nat.find hex) → R, ∑ i, a i • e i = 0 → ∀ i, a i ∈ maximalIdeal R := by
    intro a ha j
    by_contra hj
    have hu : IsUnit (a j) := by
      by_contra h'
      exact hj ((IsLocalRing.mem_maximalIdeal _).mpr h')
    have hle := Nat.find_min' hex (exists_span_fin_pred _ e he a ha j hu)
    have := j.pos
    omega
  let f := Fintype.linearCombination R e
  have hK : LinearMap.ker f ≤ maximalIdeal R • LinearMap.ker f := by
    intro a ha
    have ha' : ∑ i, a i • e i = 0 := by
      rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at ha; exact ha
    obtain ⟨b, c, hb, hc, rfl⟩ := hrel _ e he a ha' (hmin a ha')
    refine Submodule.add_mem _ (Submodule.smul_mem_smul hx ?_) (Submodule.smul_mem_smul hy ?_)
    · rw [LinearMap.mem_ker, Fintype.linearCombination_apply]; exact hb
    · rw [LinearMap.mem_ker, Fintype.linearCombination_apply]; exact hc
  have hbot : LinearMap.ker f = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) _
      (IsNoetherian.noetherian _) hK
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, he]
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨LinearMap.ker_eq_bot.mp hbot, hsurj⟩)

theorem relations_of_koszul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (x y : R)
    (hK : ∀ B C : M, x • B + y • C = 0 → ∃ w : M, B = y • w ∧ C = -(x • w))
    (n : ℕ) (e : Fin n → M) (he : Submodule.span R (Set.range e) = ⊤) (a : Fin n → R)
    (ha : ∑ i, a i • e i = 0) (hai : ∀ i, a i ∈ Ideal.span {x, y}) :
    ∃ b c : Fin n → R, ∑ i, b i • e i = 0 ∧ ∑ i, c i • e i = 0 ∧ a = x • b + y • c := by
  have hbc : ∀ i, ∃ p q : R, p * x + q * y = a i := fun i => Ideal.mem_span_pair.mp (hai i)
  choose b c hbc using hbc
  have hsum : x • (∑ i, b i • e i) + y • (∑ i, c i • e i) = 0 := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← ha]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, ← add_smul, ← hbc i, mul_comm x, mul_comm y]
  obtain ⟨w, hB, hC⟩ := hK _ _ hsum
  have hw : w ∈ Submodule.span R (Set.range e) := he ▸ Submodule.mem_top
  obtain ⟨d, hd⟩ := Submodule.mem_span_range_iff_exists_fun R |>.mp hw
  refine ⟨b - y • d, c + x • d, ?_, ?_, ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib]
    rw [hB, ← hd, Finset.smul_sum]
    simp [mul_smul]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, Finset.sum_add_distrib]
    rw [hC, ← hd, Finset.smul_sum]
    simp [mul_smul]
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← hbc i]
    ring

theorem two_le_height_of_comap (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [IsDomain A] [Algebra R A]
    [Algebra.IsIntegral R A] [FaithfulSMul R A] (h2 : ringKrullDim R = 2)
    (P : Ideal A) (hPp : P.IsPrime) (hP : P.comap (algebraMap R A) = maximalIdeal R) :
    2 ≤ P.height := by
  have hm : (maximalIdeal R).height = 2 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [h2] at this
    exact WithBot.coe_injective (this.trans rfl)
  have hmbot : maximalIdeal R ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hm
    exact absurd hm (by decide)
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmbot
  obtain ⟨q, hq, hqm⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hxm)
  have hqp : q.IsPrime := hq.1.1
  have hq1 : q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq
  have hqne : q ≠ maximalIdeal R := by
    rintro rfl
    rw [hm] at hq1
    exact absurd hq1 (by decide)
  have hqbot : q ≠ ⊥ := by
    intro h
    have := hq.1.2
    rw [h, Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at this
    exact hx0 this
  haveI : P.LiesOver (maximalIdeal R) := ⟨hP.symm⟩
  obtain ⟨Q, hQP, hQ, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q) (q := maximalIdeal R) P hqm
  have hQq : Q.comap (algebraMap R A) = q := hQo.over.symm
  have hQlt : Q < P := by
    refine lt_of_le_of_ne hQP ?_
    rintro rfl
    exact hqne (hQq.symm.trans hP)
  have hQbot : Q ≠ ⊥ := by
    rintro rfl
    apply hqbot
    rw [← hQq]
    ext z
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R A))
  have h1 : 1 ≤ Q.height := by
    rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    exact hQbot
  have h3 : Q.height + 1 ≤ P.height := Ideal.height_add_one_le_of_lt_of_isPrime hQlt
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ Q.height + 1 := by gcongr
    _ ≤ P.height := h3

theorem koszul_of_height (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [Algebra R A] [FaithfulSMul R A]
    (x y : R) (hm : maximalIdeal R = Ideal.span {x, y}) (hx : x ≠ 0)
    (hP : ∀ P : Ideal A, P.IsPrime → P.comap (algebraMap R A) = maximalIdeal R → 2 ≤ P.height)
    (B C : A) (h : x • B + y • C = 0) : ∃ w : A, B = y • w ∧ C = -(x • w) := by
  have hX : algebraMap R A x ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)).mpr hx
  rw [Algebra.smul_def, Algebra.smul_def] at h
  have hdvd : algebraMap R A x ∣ C := by
    refine GlobalTheory.dvd_of_forall_height_eq_one hX fun p _ hp1 hXp => ?_
    by_cases hYp : algebraMap R A y ∈ p
    · exfalso
      have hcomap : p.comap (algebraMap R A) = maximalIdeal R := by
        apply le_antisymm
        · exact IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance))
        · rw [hm, Ideal.span_le]
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact hXp
          · exact hYp
      have h2 := hP p inferInstance hcomap
      rw [hp1] at h2
      exact absurd h2 (by decide)
    · exact ⟨algebraMap R A y, hYp, ⟨-B, by linear_combination h⟩⟩
  obtain ⟨w', hw'⟩ := hdvd
  refine ⟨-w', ?_, ?_⟩
  · have h0 : algebraMap R A x * (B + algebraMap R A y * w') = 0 := by
      rw [hw'] at h
      linear_combination h
    have h1 := (mul_eq_zero.mp h0).resolve_left hX
    rw [Algebra.smul_def]
    linear_combination h1
  · rw [Algebra.smul_def, hw']
    ring

theorem free_of_isIntegrallyClosed : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A], (((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R) → ringKrullDim R ≤ 2 → Module.Free R A := by
  intro R A _ _ _ _ _ _ _ _ _ _ hreg hdim
  classical
  haveI : IsRegularLocalRing R := (isRegularLocalRing_iff R).mpr hreg
  haveI : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  haveI : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  have hinj := FaithfulSMul.algebraMap_injective R A
  have hreg' : ∀ r : R, r ≠ 0 → ∀ v : A, r • v = 0 → v = 0 := by
    intro r hr v hv
    rw [Algebra.smul_def] at hv
    exact (mul_eq_zero.mp hv).resolve_left ((map_ne_zero_iff _ hinj).mpr hr)
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal R))
  have hn : s.card ≤ 2 := by
    have h1 : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ 2 := hreg ▸ hdim
    rw [← hs] at h1
    exact_mod_cast h1
  have one : ∀ y : R, maximalIdeal R = Ideal.span {y} → Module.Free R A := by
    intro y hy
    have hym : y ∈ maximalIdeal R := hy ▸ Ideal.mem_span_singleton_self y
    refine free_of_relations (0 : R) y (zero_mem _) hym ?_
    intro n e _ a ha hai
    by_cases hy0 : y = 0
    · refine ⟨0, 0, by simp, by simp, ?_⟩
      funext i
      have := hai i
      rw [hy, hy0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
      simp [this]
    · have hc : ∀ i, ∃ c, a i = c * y := fun i => by
        have := hai i
        rw [hy, Ideal.mem_span_singleton'] at this
        obtain ⟨c, hc⟩ := this
        exact ⟨c, hc.symm⟩
      choose c hc using hc
      refine ⟨0, c, by simp, ?_, ?_⟩
      · apply hreg' y hy0
        rw [Finset.smul_sum, ← ha]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hc i, smul_smul, mul_comm]
      · funext i
        simp [hc i, mul_comm]
  obtain h0 | h1 | h2 : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  · refine one 0 ?_
    rw [← hspan, Finset.card_eq_zero.mp h0]
    simp
  · obtain ⟨y, rfl⟩ := Finset.card_eq_one.mp h1
    refine one y ?_
    rw [← hspan]
    simp [Ideal.span]
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
    have hm : maximalIdeal R = Ideal.span {x, y} := by
      rw [← hspan]
      simp [Ideal.span]
    have h2dim : ringKrullDim R = 2 := by
      rw [← hreg, ← hs, h2]
      rfl
    have hx0 : x ≠ 0 := by
      rintro rfl
      have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (Set.finite_singleton y)
      rw [Set.ncard_singleton] at hle
      have : Submodule.span R {y} = maximalIdeal R := by
        rw [hm]; simp [Ideal.span]
      rw [this, ← hs, h2] at hle
      omega
    have hxm : x ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
    have hym : y ∈ maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
    refine free_of_relations x y hxm hym ?_
    intro n e he a ha hai
    exact relations_of_koszul x y
      (koszul_of_height R A x y hm hx0 fun P hP hc => two_le_height_of_comap R A h2dim P hP hc)
      n e he a ha (fun i => hm ▸ hai i)

end GlobalTheory.PurFree

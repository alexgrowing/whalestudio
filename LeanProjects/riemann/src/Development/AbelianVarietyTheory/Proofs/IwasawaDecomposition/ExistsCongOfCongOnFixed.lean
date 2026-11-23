import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise

namespace GlobalTheory.InertiaMovesRoot

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem val_eq_one_of_notMem (h : IsPlaceOver A w) {s : 𝓞 E} (hs : s ∉ w.asIdeal) :
    A.valuation (algebraMap E Ω (s : E)) = 1 :=
  le_antisymm (valuation_le_one_intCl (F := E) A (algebraMap (𝓞 E) _ s))
    (not_lt.mp fun hlt => hs ((h s).mp hlt))

theorem exists_val_eq_zpow (h : IsPlaceOver A w) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {a : E} (ha : a ≠ 0) :
    ∃ m : ℤ, A.valuation (algebraMap E Ω a) = A.valuation (algebraMap E Ω (ϖ : E)) ^ m := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hϖ0' : (ϖ : E) ≠ 0 := by simpa using hϖ0
  have hv : w.intValuation ϖ = WithZero.exp (-1 : ℤ) := by
    have a1 := (w.intValuation_le_pow_iff_mem ϖ 1).2 (by rw [pow_one]; exact h1)
    have a2 : ¬ _ := fun hh => h2 ((w.intValuation_le_pow_iff_mem ϖ 2).1 hh)
    rw [← WithZero.exp_log (w.intValuation_ne_zero ϖ hϖ0), WithZero.exp_le_exp] at a1 a2
    rw [← WithZero.exp_log (w.intValuation_ne_zero ϖ hϖ0)]
    congr 1
    omega
  have hv' : w.valuation E (ϖ : E) = WithZero.exp (-1 : ℤ) := by
    rw [← hv]; exact w.valuation_of_algebraMap ϖ
  have ha' : w.valuation E a ≠ 0 := by simpa using ha
  set n := WithZero.log (w.valuation E a)
  have hu : w.valuation E (a * (ϖ : E) ^ n) = 1 := by
    rw [map_mul, map_zpow₀, hv', ← WithZero.exp_log ha', ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero]
    congr 1
    simp [n]
  obtain ⟨t, d, htd⟩ := w.exists_primeCompl_mul_eq_of_integer _ hu.le
  have hd : w.valuation E (algebraMap (𝓞 E) E d) = 1 := (w.valuation_eq_one_iff_notMem).2 d.2
  have ht : w.valuation E (algebraMap (𝓞 E) E t) = 1 := by rw [← htd, map_mul, hu, hd, one_mul]
  have ht' := val_eq_one_of_notMem h ((w.valuation_eq_one_iff_notMem).1 ht)
  have hd' := val_eq_one_of_notMem h d.2
  have e := congrArg (fun z => A.valuation (algebraMap E Ω z)) htd
  simp only [map_mul, map_zpow₀] at e
  change _ * A.valuation (algebraMap E Ω ((d : 𝓞 E) : E)) = A.valuation (algebraMap E Ω (t : E)) at e
  rw [ht', hd', mul_one] at e
  exact ⟨-n, by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left e⟩

theorem val_term_le_one {ι : Type*} (s : Finset ι) (f : ι → Ω)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → A.valuation (f i) = A.valuation (f j) → i = j)
    (hs : A.valuation (∑ i ∈ s, f i) ≤ 1) : ∀ i ∈ s, A.valuation (f i) ≤ 1 := by
  classical
  intro i hi
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => A.valuation (f i)) ⟨i, hi⟩
  by_cases h0 : f j = 0
  · refine (hmax i hi).trans ?_
    simp [h0]
  refine (hmax i hi).trans ?_
  rw [← Finset.add_sum_erase s f hj] at hs
  rwa [Valuation.map_add_eq_of_lt_left] at hs
  refine Valuation.map_sum_lt _ (by simpa using h0) fun k hk => ?_
  rw [Finset.mem_erase] at hk
  exact lt_of_le_of_ne (hmax k hk.2) fun he => hk.1 (hf j hj k hk.2 h0 he.symm).symm

theorem cong_on_adjoin (h : IsPlaceOver A w) {l : ℕ} (hl : 2 ≤ l) {ϖ : 𝓞 E} (h1 : ϖ ∈ w.asIdeal)
    (h2 : ϖ ∉ w.asIdeal ^ 2) {x : Ω} (hx : x ^ l = algebraMap E Ω (ϖ : E)) :
    x ∉ (⊥ : IntermediateField E Ω) ∧ ∀ (g : Ω ≃ₐ[E] Ω) (b : Ω),
      b ∈ IntermediateField.adjoin E {x} → A.valuation b ≤ 1 → A.valuation (g b - b) < 1 := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have hl0 : l ≠ 0 := by omega
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0, eq_comm, map_eq_zero] at hx
    exact hϖ0 (by simpa using hx)
  set t := A.valuation x with ht
  have htl : A.valuation (algebraMap E Ω (ϖ : E)) = t ^ l := by rw [← hx, map_pow]
  have ht0 : 0 < t := zero_lt_iff.mpr (by simpa [ht] using hx0)
  have ht1 : t < 1 := by
    have := (h ϖ).mpr h1
    rw [htl] at this
    exact (pow_lt_one_iff hl0).mp this
  have hinj : Function.Injective fun n : ℤ => t ^ n := zpow_right_injective₀ ht0 ht1.ne
  have hval : ∀ (a : E) (i : ℕ), algebraMap E Ω a * x ^ i ≠ 0 →
      ∃ m : ℤ, A.valuation (algebraMap E Ω a * x ^ i) = t ^ ((i : ℤ) + l * m) := by
    intro a i ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    obtain ⟨m, hm⟩ := exists_val_eq_zpow h h1 h2 ha0
    refine ⟨m, ?_⟩
    rw [map_mul, hm, htl, map_pow, zpow_add₀ ht0.ne', zpow_mul, zpow_natCast, zpow_natCast, mul_comm]
  have hmod : ∀ (i j : ℕ) (m n : ℤ), i < l → j < l → t ^ ((i : ℤ) + l * m) = t ^ ((j : ℤ) + l * n) →
      i = j := by
    intro i j m n hi hj he
    have := congrArg (· % (l : ℤ)) (hinj he)
    simp only [Int.add_mul_emod_self_left] at this
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.emod_eq_of_lt (by omega) (by omega)] at this
    omega
  constructor
  · intro hb
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hb
    obtain ⟨m, hm⟩ := hval a 0 (by simpa [ha] using hx0)
    have := hmod 0 1 m 0 (by omega) (by omega) (by rw [← hm]; simp [ha, ht])
    omega
  intro g b hb hb1
  have halg : IsAlgebraic E x := Algebra.IsAlgebraic.isAlgebraic x
  have hb' : b ∈ Algebra.adjoin E {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]; exact hb
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb'
  obtain ⟨p₀, rfl⟩ := hb'
  have hq : (X ^ l - C (ϖ : E)).Monic := monic_X_pow_sub_C _ hl0
  set p := p₀ %ₘ (X ^ l - C (ϖ : E))
  have hp : aeval x p = aeval x p₀ := aeval_modByMonic_eq_self_of_root (by simp [hx])
  have hdeg : p.natDegree < l := by
    have := natDegree_modByMonic_lt p₀ hq (by
      intro h1
      have := congrArg natDegree h1
      rw [natDegree_X_pow_sub_C, natDegree_one] at this
      exact hl0 this)
    rwa [natDegree_X_pow_sub_C] at this
  change A.valuation (aeval x p₀) ≤ 1 at hb1
  change A.valuation (g (aeval x p₀) - aeval x p₀) < 1
  rw [← hp, aeval_eq_sum_range' hdeg] at hb1 ⊢
  simp only [Algebra.smul_def] at hb1 ⊢
  have hle := val_term_le_one _ _ (fun i hi j hj h0 he => by
    obtain ⟨m, hm⟩ := hval _ i h0
    obtain ⟨n, hn⟩ := hval (p.coeff j) j (by
      intro h00
      rw [h00, map_zero] at he
      exact h0 (by simpa using he))
    exact hmod i j m n (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (by rw [← hm, ← hn, he])) hb1
  have hgx : A.valuation (g x) = t := by
    refine pow_left_injective hl0 ?_
    show _ ^ l = t ^ l
    rw [← map_pow, ← map_pow, hx, g.commutes, htl]
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  have hlt : A.valuation (algebraMap E Ω (p.coeff i) * x ^ i) < 1 := by
    refine lt_of_le_of_ne (hle i hi) fun he => ?_
    obtain ⟨m, hm⟩ := hval (p.coeff i) i (by intro h0; simp [h0] at he)
    have := hmod i 0 m 0 (Finset.mem_range.mp hi) (by omega) (by rw [← hm, he]; simp)
    omega
  refine Valuation.map_sub_lt _ ?_ hlt
  rw [map_mul g, g.commutes, map_pow g, map_mul, map_pow, hgx]
  rwa [map_mul, map_pow] at hlt

theorem mem_Ine_of_cong {σ : Ω ≃ₐ[E] Ω}
    (hσ : ∀ b : IntCl E Ω, σ • b - b ∈ primeBelow (F := E) A) : σ ∈ Ine (F := E) A := by
  have hc : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1 :=
    fun b hb => hσ ⟨b, hb.tower_top⟩
  have hdec : σ • A = A := by
    refine eq_of_valuation_lt_one_iff E fun b hb => ?_
    let b' : IntCl E Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := E) (σ • A) ↔ b' ∈ primeBelow (F := E) A
    rw [primeBelow_smul, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have := hσ (σ⁻¹ • b')
    rw [smul_inv_smul] at this
    exact ⟨fun hh => by simpa using add_mem this hh, fun hh => by simpa using sub_mem hh this⟩
  refine ⟨hdec, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den E A hx
  have hσx : A.valuation (σ x) ≤ 1 := by
    rw [A.valuation_le_one_iff, apply_mem_iff_of_mem_Dec hdec, ← A.valuation_le_one_iff]; exact hx
  have key : s * (σ x - x) = (σ t - t) - (σ s - s) * σ x := by
    rw [← e, map_mul]; ring
  have hv : A.valuation (s * (σ x - x)) < 1 := by
    rw [key]
    refine Valuation.map_sub_lt _ (hc t ht) ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hσx) (hc s hs)
  rwa [map_mul, hs1, one_mul] at hv

theorem exists_cong_of_cong_on_fixed {R S G : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [TopologicalSpace G]
    [IsTopologicalGroup G] [TopologicalSpace S] [DiscreteTopology S] [ContinuousSMul G S]
    (H : Subgroup G) [CompactSpace H] [TotallyDisconnectedSpace H] (Q : Ideal S) [Q.IsPrime]
    (g : G) (hg : ∀ b : S, (∀ k ∈ H, k • b = b) → g • b - b ∈ Q) :
    ∃ k ∈ H, ∃ k' ∈ H, ∀ b : S, (k' * g * k) • b - b ∈ Q := by
  let R' := FixedPoints.subalgebra R S H
  have hR' : ∀ b : R', ∀ k ∈ H, k • (b : S) = b := fun b k hk => b.2 ⟨k, hk⟩
  have : SMulCommClass H R' S := ⟨fun k r b => by
    change (k : G) • ((r : S) * b) = (r : S) * (k : G) • b
    rw [smul_mul', hR' r k k.2]⟩
  have : Algebra.IsInvariant R' S H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have : (g⁻¹ • Q).IsPrime := Ideal.IsPrime.smul _
  obtain ⟨k, hk⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := R') (G := H)
    Q (g⁻¹ • Q) (by
      ext b
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap,
        Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
      have := hg b (hR' b)
      change (b : S) ∈ Q ↔ g • (b : S) ∈ Q
      exact ⟨fun hh => by simpa using add_mem this hh, fun hh => by simpa using sub_mem hh this⟩)
  have hQ : (g * k) • Q = Q := by
    have hk2 : g⁻¹ • Q = (k : G) • Q := hk
    rw [mul_smul, ← hk2, smul_inv_smul]
  let φ : (S ⧸ Q) ≃ₐ[R' ⧸ Q.under R'] (S ⧸ Q) := AlgEquiv.ofRingEquiv
    (f := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv G S (g * k)) hQ.symm)
    (fun r => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q ((g * k) • (r : S)) = Ideal.Quotient.mk Q (r : S)
      rw [Ideal.Quotient.eq, mul_smul, hR' r k k.2]
      exact hg r (hR' r))
  obtain ⟨⟨k', hk'Q⟩, hk'⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under R') Q φ
  refine ⟨k, k.2, k'⁻¹, inv_mem k'.2, fun b => ?_⟩
  have h1 : Ideal.Quotient.mk Q ((k' : G) • b) = Ideal.Quotient.mk Q ((g * k) • b) :=
    DFunLike.congr_fun hk' (Ideal.Quotient.mk Q b)
  rw [eq_comm, Ideal.Quotient.eq] at h1
  have h2 : (k' : G) • Q = Q := hk'Q
  rw [← h2, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul, smul_smul] at h1
  rwa [mul_assoc]

theorem exists_mem_Ine_apply_ne : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (l : ℕ), l.Prime → ∀ (ϖ : 𝓞 E), ϖ ∈ w.asIdeal → ϖ ∉ w.asIdeal ^ 2 → ∀ x : Ω,
    x ^ l = algebraMap E Ω (ϖ : E) → ∃ σ ∈ Ine (F := E) A, σ x ≠ x := by
  intro E Ω _ _ _ _ _ A w h l hl ϖ h1 h2 x hx
  obtain ⟨hx1, hx2⟩ := cong_on_adjoin h hl.two_le h1 h2 hx
  obtain ⟨g, hg⟩ : ∃ g : Ω ≃ₐ[E] Ω, g x ≠ x := by
    by_contra hc
    push Not at hc
    exact hx1 ((InfiniteGalois.mem_bot_iff_fixed x).mpr hc)
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := MulAction.stabilizer (Ω ≃ₐ[E] Ω) x
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := E) x)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨k, hk, k', hk', hc⟩ := exists_cong_of_cong_on_fixed (R := 𝓞 E) H (primeBelow (F := E) A) g
    (fun b hb => by
      refine hx2 g b ?_ (valuation_le_one_intCl A b)
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin E {x}),
        IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hb f (hf ⟨x, IntermediateField.mem_adjoin_simple_self E x⟩)))
  refine ⟨k' * g * k, mem_Ine_of_cong hc, fun he => hg ?_⟩
  have e1 : k x = x := hk
  have e2 : k' x = x := hk'
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e1] at he
  exact k'.injective (he.trans e2.symm)

end GlobalTheory.InertiaMovesRoot

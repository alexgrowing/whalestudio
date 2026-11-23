import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply

open Polynomial

namespace GlobalTheory.NewPrime.LocalRing

theorem isUnit_of_map_ne_zero {A L : Type} [CommRing A] [Finite A] [CommRing L] [IsDomain L]
    (ψ : A →+* L) (h : ∀ x, ψ x = 0 → IsNilpotent x) {x : A} (hx : ψ x ≠ 0) : IsUnit x := by
  by_contra hu
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal (Ideal.span {x})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hxM' : x ∈ M := hxM (Ideal.mem_span_singleton_self x)
  have hle : RingHom.ker ψ ≤ M := by
    intro y hy
    obtain ⟨k, hk⟩ := h y (RingHom.mem_ker.1 hy)
    exact hM.isPrime.mem_of_pow_mem k (hk ▸ M.zero_mem)
  have : Finite (A ⧸ RingHom.ker ψ) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hmax : (RingHom.ker ψ).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (A ⧸ RingHom.ker ψ))
  have hEq := hmax.eq_of_le hM.ne_top hle
  exact hx (RingHom.mem_ker.1 (hEq ▸ hxM'))

theorem isLocalRing_of_map {A L : Type} [CommRing A] [Finite A] [CommRing L] [IsDomain L]
    (ψ : A →+* L) (h : ∀ x, ψ x = 0 → IsNilpotent x) : IsLocalRing A := by
  have : Nontrivial A := ψ.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : ψ a = 0
  · right
    refine isUnit_of_map_ne_zero ψ h ?_
    rw [map_sub, map_one, ha, sub_zero]
    exact one_ne_zero
  · exact Or.inl (isUnit_of_map_ne_zero ψ h ha)

theorem adjoinRoot_eq_zero {R : Type} [CommRing R] {g : R[X]} (hg : g.Monic) {j : ℕ}
    (hj : j < g.natDegree) {r : R} (h : AdjoinRoot.of g r * AdjoinRoot.root g ^ j = 0) : r = 0 := by
  nontriviality R
  have h1 : AdjoinRoot.mk g (C r * X ^ j) = 0 := by
    rw [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    exact h
  rw [AdjoinRoot.mk_eq_zero, ← Polynomial.modByMonic_eq_zero_iff_dvd hg] at h1
  have hdeg : (C r * X ^ j).degree < g.degree := by
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le j r) ?_
    rw [Polynomial.degree_eq_natDegree hg.ne_zero]
    exact_mod_cast hj
  rw [(Polynomial.modByMonic_eq_self_iff hg).2 hdeg] at h1
  simpa using congrArg (fun p => Polynomial.coeff p j) h1

theorem aeval_C_mul_X_coeff {ι L : Type} [Fintype ι] [CommRing L] (F : MvPolynomial ι L) (b : ι → L)
    (d : ℕ) : (MvPolynomial.aeval (fun q => C (b q) * X) F : L[X]).coeff d =
      ∑ m ∈ F.support, if m.degree = d then F.coeff m * ∏ q, b q ^ m q else 0 := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have hprod : (∏ q, (C (b q) * X : L[X]) ^ m q) = C (∏ q, b q ^ m q) * X ^ m.degree := by
    simp [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
  rw [hprod, Polynomial.algebraMap_eq, ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul_X_pow]
  rcases eq_or_ne m.degree d with hmd | hmd
  · simp [hmd]
  · simp [hmd, Ne.symm hmd]

theorem exists_point {ι L : Type} [Fintype ι] [Field L] [Infinite L] (K : Set ι)
    (F : MvPolynomial ι L) (m : ι →₀ ℕ) (hK : ∀ q ∈ K, m q = 0) (hm : F.coeff m ≠ 0) :
    ∃ b : ι → L, (∀ q ∈ K, b q = 0) ∧ (∀ q ∉ K, b q ≠ 0) ∧
      (MvPolynomial.aeval (fun q => C (b q) * X) F : L[X]).coeff m.degree ≠ 0 := by
  classical
  let H : MvPolynomial ι L := ∑ m' ∈ F.support.filter
      (fun m' => m'.degree = m.degree ∧ ∀ q ∈ K, m' q = 0), MvPolynomial.monomial m' (F.coeff m')
  have hHm : H.coeff m = F.coeff m := by
    simp only [H, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single m]
    · simp
    · intro m' _ hm'
      simp [hm']
    · intro hnot
      exfalso
      exact hnot (Finset.mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 hm, rfl, hK⟩)
  let P : MvPolynomial ι L := H * ∏ q ∈ Finset.univ.filter (fun q => q ∉ K), MvPolynomial.X q
  have hP : P ≠ 0 := by
    apply mul_ne_zero
    · intro h0
      apply hm
      rw [← hHm, h0, MvPolynomial.coeff_zero]
    · exact Finset.prod_ne_zero_iff.2 fun q _ => MvPolynomial.X_ne_zero q
  obtain ⟨x, hx⟩ : ∃ x, MvPolynomial.eval x P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hP (MvPolynomial.funext fun x => by simpa using hcon x)
  have hxH : MvPolynomial.eval x H ≠ 0 := fun h0 => hx (by simp [P, h0])
  have hxq : ∀ q ∉ K, x q ≠ 0 := by
    intro q hq h0
    apply hx
    simp only [P, map_mul, map_prod, MvPolynomial.eval_X]
    rw [Finset.prod_eq_zero (i := q) (by simp [hq]) h0, mul_zero]
  refine ⟨fun q => if q ∈ K then 0 else x q, fun q hq => by simp [hq],
    fun q hq => by simp [hq, hxq q hq], ?_⟩
  have key : MvPolynomial.eval x H = ∑ m' ∈ F.support, if m'.degree = m.degree then
      F.coeff m' * ∏ q, (if q ∈ K then 0 else x q) ^ m' q else 0 := by
    simp only [H, Finset.sum_filter, map_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    by_cases hd : m'.degree = m.degree
    · by_cases hz : ∀ q ∈ K, m' q = 0
      · rw [if_pos ⟨hd, hz⟩, if_pos hd, MvPolynomial.eval_monomial,
          Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
        congr 1
        refine Finset.prod_congr rfl fun q _ => ?_
        by_cases hq : q ∈ K
        · simp [hq, hz q hq]
        · simp [hq]
      · rw [if_neg (fun h => hz h.2), if_pos hd, map_zero]
        push Not at hz
        obtain ⟨q, hq, hq0⟩ := hz
        rw [Finset.prod_eq_zero (Finset.mem_univ q) (by simp [hq, hq0]), mul_zero]
    · rw [if_neg (fun h => hd h.1), if_neg hd, map_zero]
  rw [aeval_C_mul_X_coeff, ← key]
  exact hxH

theorem exists_primitive {k L ι : Type} [Field k] [Finite k] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L] [Finite ι] (b : ι → L) :
    ∃ α : L, ∀ q, ∃ p : k[X], aeval α p = b q := by
  classical
  let E := IntermediateField.adjoin k (Set.range b)
  haveI : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_bot k E
  refine ⟨(α : L), fun q => ?_⟩
  have hbq : b q ∈ E := IntermediateField.subset_adjoin k _ ⟨q, rfl⟩
  have hmem : (⟨b q, hbq⟩ : E) ∈ (IntermediateField.adjoin k {α}).toSubalgebra := by
    rw [IntermediateField.mem_toSubalgebra, hα]
    exact IntermediateField.mem_top
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite k α),
    Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  refine ⟨p, ?_⟩
  have h1 : aeval (E.val α) p = E.val (aeval α p) := Polynomial.aeval_algHom_apply E.val α p
  rw [show (α : L) = E.val α from rfl, h1]
  have h2 : (aeval α) p = ⟨b q, hbq⟩ := hp
  rw [h2]
  rfl

private theorem finite_adjoinRoot_of_monic {R : Type} [CommRing R] [Finite R] {g : R[X]}
    (hg : g.Monic) : Finite (AdjoinRoot g) := by
  haveI := (AdjoinRoot.powerBasis' hg).finite
  exact Module.finite_of_finite R

theorem exists_lift {R k L ι : Type} [CommRing R] [Finite R] [Field k] [Finite k] [Field L]
    [Algebra k L] [Algebra.IsAlgebraic k L] [Finite ι] (φ : R →+* k) (hφ : Function.Surjective φ)
    (π : R) (hπ : ∀ x, φ x = 0 → π ∣ x) (b : ι → L) :
    ∃ (S : Type) (_ : CommRing S) (_ : Finite S) (f : R →+* S) (ψ : S →+* L),
      Function.Injective f ∧ (∀ x, ψ (f x) = algebraMap k L (φ x)) ∧
      (∀ x, ψ x = 0 → f π ∣ x) ∧ ∀ q, ∃ s, ψ s = b q := by
  classical
  obtain ⟨α, hα⟩ := exists_primitive (k := k) b
  choose p hp using hα
  have hint : IsIntegral k α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  obtain ⟨g, hgmap, hgdeg, hgmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective φ hφ (minpoly k α))) (minpoly.monic hint)
  have hdegpos : 0 < g.natDegree := by
    rw [hgdeg]
    exact minpoly.natDegree_pos hint
  have hg0 : g.eval₂ ((algebraMap k L).comp φ) α = 0 := by
    rw [← Polynomial.eval₂_map, hgmap, ← Polynomial.aeval_def]
    exact minpoly.aeval k α
  refine ⟨AdjoinRoot g, inferInstance, finite_adjoinRoot_of_monic hgmon, AdjoinRoot.of g,
    AdjoinRoot.lift ((algebraMap k L).comp φ) α hg0, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have h0 : AdjoinRoot.of g (x - y) * AdjoinRoot.root g ^ 0 = 0 := by
      rw [map_sub, hxy, sub_self, zero_mul]
    exact sub_eq_zero.1 (adjoinRoot_eq_zero hgmon hdegpos h0)
  · intro x
    rw [AdjoinRoot.lift_of]
    rfl
  · intro s hs
    obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective s
    rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← Polynomial.aeval_def] at hs
    obtain ⟨t, ht⟩ := minpoly.dvd k α hs
    obtain ⟨t', rfl⟩ := Polynomial.map_surjective φ hφ t
    have he : ∀ n, (h - g * t').coeff n ∈ Ideal.span {π} := by
      intro n
      refine Ideal.mem_span_singleton.2 (hπ _ ?_)
      rw [← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_mul, hgmap, ht, sub_self,
        Polynomial.coeff_zero]
    have he' : h - g * t' ∈ Ideal.span {C π} := by
      have h3 := (Ideal.mem_map_C_iff (I := Ideal.span {π})).2 he
      rwa [Ideal.map_span, Set.image_singleton] at h3
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 he'
    refine ⟨AdjoinRoot.mk g u, ?_⟩
    have hsplit : h = C π * u + g * t' := by
      rw [← hu]
      ring
    rw [hsplit, map_add, map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero, AdjoinRoot.mk_C]
  · intro q
    obtain ⟨r, hr⟩ := Polynomial.map_surjective φ hφ (p q)
    refine ⟨AdjoinRoot.mk g r, ?_⟩
    rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, hr, ← Polynomial.aeval_def, hp q]

theorem exists_truncation {R L : Type} [CommRing R] [Finite R] [Field L] (ψ : R →+* L) (π : R)
    (n w N : ℕ) (hn : π ^ n = 0) (hπ : ∀ x, ψ x = 0 → π ∣ x) (P : R[X]) (d : ℕ) (hd : d ≤ w)
    (hP : ψ (P.coeff d) ≠ 0) :
    IsLocalRing (AdjoinRoot (X ^ (N + 1) : R[X])) ∧
      AdjoinRoot.mk (X ^ (N + 1) : R[X]) P ∣ AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ (n * w) := by
  classical
  have hnil : ∀ x, ψ x = 0 → IsNilpotent x := fun x hx => by
    obtain ⟨c, rfl⟩ := hπ x hx
    exact ⟨n, by rw [mul_pow, hn, zero_mul]⟩
  have hT : (X ^ (N + 1) : R[X]).Monic := Polynomial.monic_X_pow _
  have := finite_adjoinRoot_of_monic hT
  have hT0 : (X ^ (N + 1) : R[X]).eval₂ ψ 0 = 0 := by simp
  have hroot : AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ (N + 1) = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]
  have hnil' : ∀ z, AdjoinRoot.lift ψ (0 : L) hT0 z = 0 → IsNilpotent z := by
    intro z hz
    obtain ⟨h, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero] at hz
    have hsplit : h = C (h.coeff 0) + X * h.divX :=
      (Polynomial.X_mul_divX_add h).symm.trans (add_comm _ _)
    rw [hsplit, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    refine Commute.isNilpotent_add (Commute.all _ _) ((hnil _ hz).map _) ?_
    exact ⟨N + 1, by rw [mul_pow, hroot, zero_mul]⟩
  refine ⟨isLocalRing_of_map _ hnil', ?_⟩
  have hex : ∃ i, ψ (P.coeff i) ≠ 0 := ⟨d, hP⟩
  obtain ⟨d0, hd0, hmin⟩ : ∃ d0, ψ (P.coeff d0) ≠ 0 ∧ ∀ i < d0, ψ (P.coeff i) = 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => not_not.1 (Nat.find_min hex hi)⟩
  have hd0le : d0 ≤ d := by
    by_contra hlt
    exact hP (hmin d (by omega))
  have hbelow : ∀ i, ∃ c, i < d0 → P.coeff i = π * c := by
    intro i
    by_cases hi : i < d0
    · obtain ⟨c, hc⟩ := hπ _ (hmin i hi)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose c hc using hbelow
  obtain ⟨A', hA'⟩ : ∃ A' : R[X], A' = ∑ i ∈ Finset.range d0, C (c i) * X ^ i := ⟨_, rfl⟩
  have hA'coeff : ∀ j, A'.coeff j = if j < d0 then c j else 0 := by
    intro j
    rw [hA', Polynomial.finsetSum_coeff]
    simp [Polynomial.coeff_C_mul_X_pow]
  have hQ : X ^ d0 ∣ P - C π * A' := by
    rw [Polynomial.X_pow_dvd_iff]
    intro j hj
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hc j hj, hA'coeff, if_pos hj, sub_self]
  obtain ⟨V, hV⟩ := hQ
  have hV0 : V.coeff 0 = P.coeff d0 := by
    have h1 : (X ^ d0 * V).coeff d0 = V.coeff 0 := by
      rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
    rw [← h1, ← hV, Polynomial.coeff_sub, Polynomial.coeff_C_mul, hA'coeff, if_neg (lt_irrefl d0),
      mul_zero, sub_zero]
  have hu : IsUnit (AdjoinRoot.mk (X ^ (N + 1) : R[X]) V) := by
    refine isUnit_of_map_ne_zero _ hnil' ?_
    rw [AdjoinRoot.lift_mk, Polynomial.eval₂_at_zero, hV0]
    exact hd0
  have hy : AdjoinRoot.mk (X ^ (N + 1) : R[X]) P =
      AdjoinRoot.of (X ^ (N + 1) : R[X]) π * AdjoinRoot.mk (X ^ (N + 1) : R[X]) A' +
        AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ d0 * AdjoinRoot.mk (X ^ (N + 1) : R[X]) V := by
    have hP' : P = C π * A' + X ^ d0 * V := by
      rw [← hV]
      ring
    rw [hP', map_add, map_mul, map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  have hπ0 : AdjoinRoot.of (X ^ (N + 1) : R[X]) π ^ n = 0 := by
    rw [← map_pow, hn, map_zero]
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  set J := Ideal.span {AdjoinRoot.mk (X ^ (N + 1) : R[X]) P} with hJ
  have h1 : Ideal.Quotient.mk J (AdjoinRoot.mk (X ^ (N + 1) : R[X]) P) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [hy, map_add] at h1
  have h2 := eq_neg_of_add_eq_zero_right h1
  have h3 : Ideal.Quotient.mk J ((AdjoinRoot.root (X ^ (N + 1) : R[X]) ^ d0 *
      AdjoinRoot.mk (X ^ (N + 1) : R[X]) V) ^ n) = 0 := by
    rw [map_pow, h2, neg_pow, ← map_pow, mul_pow, hπ0, zero_mul, map_zero, mul_zero]
  rw [mul_pow, ← pow_mul, map_mul] at h3
  have h4 := ((hu.pow n).map (Ideal.Quotient.mk J)).mul_left_eq_zero.1 h3
  have hw : n * w = d0 * n + n * (w - d0) := by
    have hdw : d0 ≤ w := hd0le.trans hd
    rw [mul_comm d0 n, ← mul_add, Nat.add_sub_cancel' hdw]
  rw [hw, pow_add (AdjoinRoot.root (X ^ (N + 1) : R[X])) (d0 * n) (n * (w - d0)), map_mul, h4,
    zero_mul]

theorem exists_finite_local_ring (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (l : O) (e w : ℕ) (ι : Type) [Fintype ι] (K : Set ι)
    (F : MvPolynomial ι O) (hl : IsDiscreteValuationRing.addVal O l = e)
    (hF : ∃ m : ι →₀ ℕ, m.degree < w + 1 ∧ (∀ q ∈ K, m q = 0) ∧ IsUnit (F.coeff m)) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : Finite A) (_ : Algebra O A) (t : A)
      (a : ι → A), (∀ x ∈ Ideal.span {l} * IsLocalRing.maximalIdeal O, algebraMap O A x = 0) ∧
      t ^ (2 * (e + 1) * w + 2) = 0 ∧ algebraMap O A l * t ^ (2 * (e + 1) * w + 1) ≠ 0 ∧
      (∀ q ∈ K, a q = 0) ∧ (∀ q ∉ K, IsUnit (a q)) ∧
      MvPolynomial.aeval (fun q => a q * t) F ∣ t ^ ((e + 1) * w) := by
  classical
  obtain ⟨m, hmw, hmK, hmu⟩ := hF
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  obtain ⟨e', u, hlu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have he' : e' = e := by
    have h1 := IsDiscreteValuationRing.addVal_def l u hϖ e' hlu
    rw [hl] at h1
    exact_mod_cast h1.symm
  rw [he'] at hlu
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨I, hI⟩ : ∃ I : Ideal O, I = Ideal.span {l} * IsLocalRing.maximalIdeal O := ⟨_, rfl⟩
  have hϖmem : ϖ ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hϖ.not_isUnit)
  have hϖI : ϖ ^ (e + 1) ∈ I := by
    have h1 : ϖ ^ (e + 1) = ((↑u⁻¹ : O) * l) * ϖ := by
      rw [hlu, ← mul_assoc (↑u⁻¹ : O), Units.inv_mul, one_mul, pow_succ]
    rw [h1, hI]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton.2 (dvd_mul_left l _)) hϖmem
  have hpow : IsLocalRing.maximalIdeal O ^ (e + 1) ≤ I := by
    rw [hmax, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
    exact hϖI
  have : Finite (O ⧸ IsLocalRing.maximalIdeal O) :=
    (inferInstance : Finite (IsLocalRing.ResidueField O))
  have : Finite (O ⧸ IsLocalRing.maximalIdeal O ^ (e + 1)) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _
  have : Finite (O ⧸ I) := Finite.of_surjective (Ideal.Quotient.factor hpow)
    (Ideal.Quotient.factor_surjective hpow)
  have hIm : I ≤ IsLocalRing.maximalIdeal O := by
    rw [hI]
    exact Ideal.mul_le_inf.trans inf_le_right
  have hIle : ∀ x ∈ I, IsLocalRing.residue O x = 0 := fun x hx =>
    (IsLocalRing.residue_eq_zero_iff x).2 (hIm hx)
  obtain ⟨φ, hφdef⟩ : ∃ φ : O ⧸ I →+* IsLocalRing.ResidueField O,
      ∀ x, φ (Ideal.Quotient.mk I x) = IsLocalRing.residue O x :=
    ⟨Ideal.Quotient.lift I (IsLocalRing.residue O) hIle, fun x => Ideal.Quotient.lift_mk I _ hIle⟩
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨Ideal.Quotient.mk I x, hφdef x⟩
  have hker : ∀ x : O ⧸ I, φ x = 0 → Ideal.Quotient.mk I ϖ ∣ x := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hφdef, IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton] at hx
    exact map_dvd _ hx
  obtain ⟨χ, hχdef⟩ : ∃ χ : O →+* AlgebraicClosure (IsLocalRing.ResidueField O),
      ∀ x, χ x = algebraMap _ _ (IsLocalRing.residue O x) :=
    ⟨(algebraMap _ _).comp (IsLocalRing.residue O), fun x => rfl⟩
  have hcoef : (F.map χ).coeff m ≠ 0 := by
    rw [MvPolynomial.coeff_map, hχdef]
    intro h0
    exact (hmu.map (IsLocalRing.residue O)).ne_zero
      ((map_eq_zero_iff _ (algebraMap _ _).injective).1 h0)
  obtain ⟨b, hbK, hbnK, hbcoef⟩ := exists_point K (F.map χ) m hmK hcoef
  obtain ⟨S, _, _, f, ψ, hfinj, hψf, hψker, hψsurj⟩ :=
    exists_lift φ hφsurj (Ideal.Quotient.mk I ϖ) hker b
  choose s hs using hψsurj
  have : Nontrivial S := ψ.domain_nontrivial
  obtain ⟨a, haK, hanK⟩ : ∃ a : ι → S, (∀ q ∈ K, a q = 0) ∧ (∀ q ∉ K, a q = s q) :=
    ⟨fun q => if q ∈ K then 0 else s q, fun q hq => if_pos hq, fun q hq => if_neg hq⟩
  have hψa : ∀ q, ψ (a q) = b q := by
    intro q
    by_cases hq : q ∈ K
    · rw [haK q hq, map_zero, hbK q hq]
    · rw [hanK q hq, hs]
  have hfπ : f (Ideal.Quotient.mk I ϖ) ^ (e + 1) = 0 := by
    rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 hϖI, map_zero]
  have hnilS : ∀ x, ψ x = 0 → IsNilpotent x := by
    intro x hx
    obtain ⟨c, rfl⟩ := hψker x hx
    exact ⟨e + 1, by rw [mul_pow, hfπ, zero_mul]⟩
  have haU : ∀ q ∉ K, IsUnit (a q) := by
    intro q hq
    refine isUnit_of_map_ne_zero ψ hnilS ?_
    rw [hψa]
    exact hbnK q hq
  obtain ⟨hOS, hOSdef⟩ : ∃ h : O →+* S, ∀ x, h x = f (Ideal.Quotient.mk I x) :=
    ⟨f.comp (Ideal.Quotient.mk I), fun _ => rfl⟩
  obtain ⟨Pp, hPp⟩ : ∃ P : S[X], P = MvPolynomial.eval₂ (C.comp hOS) (fun q => C (a q) * X) F :=
    ⟨_, rfl⟩
  have hmapP : Pp.map ψ = MvPolynomial.aeval (fun q => C (b q) * X) (F.map χ) := by
    have e1 : (Polynomial.mapRingHom ψ).comp (C.comp hOS) = C.comp χ := by
      refine RingHom.ext fun x => ?_
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, hOSdef, hψf,
        hφdef, hχdef]
    have e2 : (⇑(Polynomial.mapRingHom ψ) ∘ fun q => C (a q) * X) = fun q => C (b q) * X := by
      funext q
      simp [hψa]
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, Polynomial.algebraMap_eq, hPp,
      ← Polynomial.coe_mapRingHom, MvPolynomial.eval₂_comp_left, e1, e2]
  have hcoefP : ψ (Pp.coeff m.degree) ≠ 0 := by
    rw [← Polynomial.coeff_map, hmapP]
    exact hbcoef
  obtain ⟨hloc, hdiv⟩ := exists_truncation ψ (f (Ideal.Quotient.mk I ϖ)) (e + 1) w
    (2 * (e + 1) * w + 1) hfπ hψker Pp m.degree (by omega) hcoefP
  have hTmon : (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]).Monic := Polynomial.monic_X_pow _
  have := finite_adjoinRoot_of_monic hTmon
  let alg : Algebra O (AdjoinRoot (X ^ (2 * (e + 1) * w + 1 + 1) : S[X])) :=
    ((AdjoinRoot.of _).comp hOS).toAlgebra
  refine ⟨AdjoinRoot (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]), inferInstance, hloc, inferInstance, alg,
    AdjoinRoot.root _, fun q => AdjoinRoot.of _ (a q), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, hOSdef, Ideal.Quotient.eq_zero_iff_mem.2 (hI ▸ hx), map_zero, map_zero]
  · rw [show 2 * (e + 1) * w + 2 = 2 * (e + 1) * w + 1 + 1 by ring, ← AdjoinRoot.mk_X, ← map_pow]
    exact AdjoinRoot.mk_self
  · intro h0
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply] at h0
    have h1 := adjoinRoot_eq_zero (r := hOS l) (j := 2 * (e + 1) * w + 1) hTmon
      (by rw [Polynomial.natDegree_X_pow]; omega) h0
    rw [hOSdef, ← map_zero f] at h1
    have hlI : l ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 (hfinj h1)
    rw [hI, hmax, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton] at hlI
    obtain ⟨c, hc⟩ := hlI
    apply hϖ.not_isUnit
    have h2 : l * 1 = l * (ϖ * c) := by
      rw [mul_one, ← mul_assoc]
      exact hc
    have h3 := mul_left_cancel₀ hl0 h2
    exact ⟨⟨ϖ, c, h3.symm, by rw [mul_comm]; exact h3.symm⟩, rfl⟩
  · intro q hq
    dsimp only
    rw [haK q hq, map_zero]
  · intro q hq
    exact (haU q hq).map _
  · have hev : MvPolynomial.aeval (fun q => AdjoinRoot.of (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]) (a q) *
        AdjoinRoot.root _) F = AdjoinRoot.mk (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]) Pp := by
      have e3 : (AdjoinRoot.mk (X ^ (2 * (e + 1) * w + 1 + 1) : S[X])).comp (C.comp hOS) =
          (AdjoinRoot.of _).comp hOS := by
        refine RingHom.ext fun x => ?_
        simp only [RingHom.comp_apply, AdjoinRoot.mk_C]
      have e4 : (⇑(AdjoinRoot.mk (X ^ (2 * (e + 1) * w + 1 + 1) : S[X])) ∘ fun q => C (a q) * X) =
          fun q => AdjoinRoot.of (X ^ (2 * (e + 1) * w + 1 + 1) : S[X]) (a q) * AdjoinRoot.root _ := by
        funext q
        simp [AdjoinRoot.mk_C, AdjoinRoot.mk_X]
      rw [MvPolynomial.aeval_def, RingHom.algebraMap_toAlgebra, hPp, MvPolynomial.eval₂_comp_left,
        e3, e4]
    rw [hev]
    exact hdiv

end GlobalTheory.NewPrime.LocalRing

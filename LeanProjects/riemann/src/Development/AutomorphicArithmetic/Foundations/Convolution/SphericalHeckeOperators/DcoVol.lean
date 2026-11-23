import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem meas_union {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (A I J : Subgroup G) (t : G)
    (hJ : ∀ x, x ∈ J ↔ t⁻¹ * x * t ∈ I) (hI : MeasurableSet (I : Set G))
    [Finite (A ⧸ J.subgroupOf A)] :
    μ {g | ∃ x ∈ A, ∃ y ∈ I, g = x * t * y} = J.relIndex A * μ (I : Set G) := by
  classical
  let S : A ⧸ J.subgroupOf A → Set G := fun q => (fun g => ((q.out : G) * t)⁻¹ * g) ⁻¹' (I : Set G)
  have hU : {g | ∃ x ∈ A, ∃ y ∈ I, g = x * t * y} = ⋃ q, S q := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, S, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      refine ⟨((⟨x, hx⟩ : A) : A ⧸ J.subgroupOf A), ?_⟩
      have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨x, hx⟩ : A) : A ⧸ J.subgroupOf A))
      rw [Subgroup.mem_subgroupOf, hJ] at h
      have := I.mul_mem h hy
      simpa [mul_assoc] using this
    · rintro ⟨q, hq⟩
      exact ⟨q.out, q.out.2, _, hq, by group⟩
  have hd : Pairwise (Function.onFun Disjoint S) := by
    intro p q hpq
    refine Set.disjoint_left.2 fun g hp hq => hpq ?_
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      Subgroup.mem_subgroupOf, hJ]
    have := I.mul_mem hp (I.inv_mem hq)
    simpa [mul_assoc] using this
  rw [hU, measure_iUnion hd (fun q => measurable_const_mul _ hI)]
  simp only [S, measure_preimage_mul]
  rw [ENNReal.tsum_const, Subgroup.relIndex, Subgroup.index, ENat.card_eq_coe_natCard]
  simp

private theorem index_modular {B : Type*} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [LocallyCompactSpace B] [T2Space B] (A J : Subgroup B) (t : B) (hAc : IsCompact (A : Set B)) (hAo : IsOpen (A : Set B))
    (hJ : ∀ x, x ∈ J ↔ t⁻¹ * x * t ∈ A) (hJA : J ≤ A) :
    Measure.modularCharacter t * J.relIndex A = 1 := by
  borelize B
  let ν : Measure B := Measure.haar
  have hJs : (J : Set B) = (fun g => t⁻¹ * g) ⁻¹' ((fun g => g * t) ⁻¹' (A : Set B)) := by
    ext x; exact hJ x
  have hJo : IsOpen (J : Set B) := by
    rw [hJs]; exact (hAo.preimage (by fun_prop)).preimage (by fun_prop)
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hAc
  haveI : Finite (A ⧸ J.subgroupOf A) :=
    Subgroup.quotient_finite_of_isOpen _ (hJo.preimage continuous_subtype_val)
  have h1 := meas_union ν A J J 1 (by simp) hJo.measurableSet
  have h2 : {g | ∃ x ∈ A, ∃ y ∈ J, g = x * 1 * y} = (A : Set B) := by
    ext g
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact A.mul_mem (by simpa using hx) (hJA hy)
    · intro hg
      exact ⟨g, hg, 1, J.one_mem, by simp⟩
  have h3 : ν (J : Set B) = Measure.modularCharacter t * ν (A : Set B) := by
    rw [hJs, measure_preimage_mul, ← Measure.map_apply (measurable_mul_const t) hAo.measurableSet,
      Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure _ ν hAc.closure,
      ← Measure.modularCharacterFun_eq_haarScalarFactor]
    rfl
  rw [h2, h3, ← mul_assoc] at h1
  have h0 : ν (A : Set B) ≠ 0 := hAo.measure_ne_zero ν ⟨1, A.one_mem⟩
  have h4 : (J.relIndex A : ENNReal) * Measure.modularCharacter t = 1 := by
    apply (ENNReal.mul_left_inj h0 hAc.measure_lt_top.ne).1
    rw [← h1, one_mul]
  rw [mul_comm] at h4
  exact_mod_cast h4

private theorem meas_dcoset {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (B I : Subgroup G)
    [LocallyCompactSpace B] (hB : IsClosed (B : Set G)) (hIc : IsCompact (I : Set G)) (hIo : IsOpen (I : Set G))
    (t : B) (h1 : ∀ x ∈ B, x ∈ I → (t : G) * x * (t : G)⁻¹ ∈ I)
    (h2 : ∀ k ∈ I, ∃ x ∈ B, x ∈ I ∧ ∃ z, (t : G)⁻¹ * z * t ∈ I ∧ k = x * z) :
    Measure.modularCharacter t * μ {g | ∃ x ∈ I, ∃ y ∈ I, g = x * t * y} = μ (I : Set G) := by
  let J : Subgroup G := I.comap (MulAut.conj (t : G)⁻¹).toMonoidHom
  have hJ : ∀ x, x ∈ J ↔ (t : G)⁻¹ * x * t ∈ I := fun x => by simp [J]
  have hJo : IsOpen (J : Set G) := by
    have : (J : Set G) = (fun x => (t : G)⁻¹ * x * t) ⁻¹' (I : Set G) := Set.ext hJ
    rw [this]; exact hIo.preimage (by fun_prop)
  have hAc : IsCompact ((I ⊓ B : Subgroup G) : Set G) := hIc.inter_right hB
  haveI : CompactSpace (I ⊓ B : Subgroup G) := isCompact_iff_compactSpace.1 hAc
  haveI : Finite ((I ⊓ B : Subgroup G) ⧸ J.subgroupOf (I ⊓ B)) :=
    Subgroup.quotient_finite_of_isOpen _ (hJo.preimage continuous_subtype_val)
  have e1 := meas_union μ (I ⊓ B) I J t hJ hIo.measurableSet
  have e2 : {g | ∃ x ∈ I, ∃ y ∈ I, g = x * t * y} = {g | ∃ x ∈ I ⊓ B, ∃ y ∈ I, g = x * t * y} := by
    ext g
    constructor
    · rintro ⟨k, hk, y, hy, rfl⟩
      obtain ⟨x, hxB, hxI, z, hz, rfl⟩ := h2 k hk
      exact ⟨x, ⟨hxI, hxB⟩, _, I.mul_mem hz hy, by group⟩
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, hx.1, y, hy, rfl⟩
  have e3 := index_modular (I.subgroupOf B) (J.subgroupOf B) t
    (hB.isClosedEmbedding_subtypeVal.isCompact_preimage hIc) (hIo.preimage continuous_subtype_val)
    (fun x => by rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hJ]; rfl)
    (fun x hx => by
      rw [Subgroup.mem_subgroupOf, hJ] at hx
      have := h1 _ (B.mul_mem (B.mul_mem (B.inv_mem t.2) x.2) t.2) hx
      rw [Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using this)
  have e4 : (J.subgroupOf B).relIndex (I.subgroupOf B) = J.relIndex (I ⊓ B) := by
    rw [← Subgroup.inf_subgroupOf_right I B, Subgroup.relIndex_subgroupOf inf_le_right]
  rw [e4] at e3
  rw [e2, e1, ← mul_assoc]
  have e5 : (Measure.modularCharacter t : ENNReal) * (J.relIndex (I ⊓ B) : ENNReal) = 1 := by
    exact_mod_cast e3
  rw [e5, one_mul]

private theorem conj_mem {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    (a : Fin n → ℤ) {g : GL (Fin n) F} (hg : g ∈ iwahori F n)
    (h : ∀ i j, a i < a j → (g : Matrix (Fin n) (Fin n) F) i j = 0) :
    torusPow F n a * g * (torusPow F n a)⁻¹ ∈ iwahori F n := by
  have he : ∀ i j, ((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (a i - a j) * (g : Matrix (Fin n) (Fin n) F) i j := by
    intro i j
    rw [← torusPow_neg, Units.val_mul, Units.val_mul, coe_torusPow, coe_torusPow, Matrix.mul_diagonal,
      Matrix.diagonal_mul, sub_eq_add_neg, zpow_add₀ (GLnLocal.uniformizer_ne_zero F), Pi.neg_apply]
    ring
  have hle : ∀ i j, ValuativeRel.valuation F
      (((torusPow F n a * g * (torusPow F n a)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j) ≤
      ValuativeRel.valuation F ((g : Matrix (Fin n) (Fin n) F) i j) := by
    intro i j
    rw [he]
    rcases lt_or_ge (a i) (a j) with hij | hij
    · rw [h i j hij, mul_zero]
    · simpa using Parabolic.valuation_zpow_mul_le_pow_mul (F := F) (e := 0) (z := a i - a j)
        (x := (g : Matrix (Fin n) (Fin n) F) i j) (by simpa using hij)
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hg
  refine (mem_iwahori_iff F n).2 ⟨fun i j => (hle i j).trans (h1 i j),
    fun i j hij => (hle i j).trans_lt (h2 i j hij), fun i => ?_⟩
  rw [he, sub_self, zpow_zero, one_mul, h3]

theorem UpperTheory.ConvolutionTheory.H.dcoVol :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (a : Fin n → ℤ), Antitone a →
      halfModulus F a ^ 2 * (μ.real (dco F a) : ℂ) = (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) := by
  intro F _ _ _ _ n _ _ μ _ a ha
  have key := meas_dcoset μ (blockUpper F n (id : Fin n → Fin n)) (iwahori F n) (Measures.isClosed_blockUpper F n _)
    (isCompact_iwahori F n) (isOpen_iwahori F n) (torusBorel F n a)
    (fun x hxB hxI => conj_mem a hxI fun i j hij =>
      (mem_blockUpper F n).1 hxB (lt_of_not_ge fun h => (ha h).not_gt hij))
    (fun k hk => by
      obtain ⟨x, hx, y, hy, z, hz, rfl⟩ :=
        Parabolic.iwahori_iwahoriFactorization' (β := (id : Fin n → Fin n)) monotone_id k hk
      refine ⟨x * y, mul_mem (Parabolic.unipotentRadical_le_blockUpper hx.2)
        (Parabolic.levi_le_blockUpper hy.2), mul_mem hx.1 hy.1, z, ?_, rfl⟩
      have := conj_mem (-a) hz.1 fun i j hij =>
        (Parabolic.mem_oppositeUnipotentRadical.1 hz.2).1 i j
          (lt_of_not_ge fun h => (ha h).not_gt (neg_lt_neg_iff.1 hij))
      rwa [torusPow_neg, inv_inv] at this)
  have h2 : halfModulus F a ^ 2 = ((Measure.modularCharacter (torusBorel F n a) : ℝ) : ℂ) := by
    rw [halfModulus_eq, modularCharacter_torusBorel, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, sqrtQ_sq]
    push_cast
    rfl
  rw [h2, measureReal_def, measureReal_def, ← key, ENNReal.toReal_mul, ENNReal.coe_toReal, Complex.ofReal_mul]
  rfl

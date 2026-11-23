import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.InertiaInvariantValuationUniformizerBound

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem zero_one_mem_gammaSet_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {q : ℕ} (hq2 : 2 ≤ q) {a : Ω} (ha : a ^ q = a) : a ∈ A := by
  rcases eq_or_ne a 0 with rfl | h0
  · exact A.zero_mem
  rcases A.mem_or_inv_mem a with h | h
  · exact h
  · have h1 : a * a ^ (q - 2) = 1 := by
      rw [← pow_succ', show q - 2 + 1 = q - 1 by omega]
      have : a ^ q = a ^ (q - 1) * a := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [this] at ha
      exact (mul_eq_right₀ h0).1 ha
    rw [eq_inv_of_mul_eq_one_left h1, ← inv_pow]
    exact A.pow_mem h _

private theorem eq_of_pow_eq_self_of_valuation_sub_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {q : ℕ} (hq : A.valuation (q : Ω) < 1) {a b : Ω} (ha : a ∈ A) (hb : b ∈ A) (ha' : a ^ q = a) (hb' : b ^ q = b) (hab : A.valuation (a - b) < 1) : a = b := by
  by_contra hne
  have hS : (∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i)) = 1 := by
    have h := geom_sum₂_mul a b q
    rw [ha', hb'] at h
    have hsub : a - b ≠ 0 := sub_ne_zero.2 hne
    exact (mul_eq_right₀ hsub).1 h
  set a' : A := ⟨a, ha⟩
  set b' : A := ⟨b, hb⟩
  have hS' : (∑ i ∈ Finset.range q, a' ^ i * b' ^ (q - 1 - i)) = 1 := by
    apply Subtype.ext
    simpa using hS
  have hr : IsLocalRing.residue A a' = IsLocalRing.residue A b' := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hab
  have hq' : IsLocalRing.residue A (q : A) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hq
  have := congrArg (IsLocalRing.residue A) hS'
  rw [map_sum, map_one] at this
  simp only [map_mul, map_pow, ← hr] at this
  rw [Finset.sum_congr rfl (fun i hi => by rw [← pow_add, Nat.add_sub_cancel' (by have := Finset.mem_range.1 hi; omega)])] at this
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← map_natCast (IsLocalRing.residue A), hq', zero_mul] at this
  exact zero_ne_one this

private theorem fin_lemma_3 {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l : ℕ} [hp : Fact l.Prime] (hl : A.valuation (l : Ω) < 1) (a : A) (halg : IsAlgebraic ℚ (a : Ω)) :
    ∃ q : ℕ, 2 ≤ q ∧ A.valuation (q : Ω) < 1 ∧ A.valuation ((a : Ω) ^ q - a) < 1 := by
  have hlK : ((l : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hl
  haveI : CharP (IsLocalRing.ResidueField A) l := (CharP.charP_iff_prime_eq_zero hp.out).2 hlK
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  obtain ⟨Q, hQ0, hQ⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 halg
  have hc0 : Q.content ≠ 0 := by
    rwa [Ne, Polynomial.content_eq_zero_iff]
  have hQ'Ω : Polynomial.aeval (a : Ω) Q.primPart = 0 := by
    have h := hQ
    rw [Polynomial.eq_C_content_mul_primPart Q, map_mul, Polynomial.aeval_C] at h
    refine (mul_eq_zero.1 h).resolve_left ?_
    rw [IsScalarTower.algebraMap_apply ℤ ℚ Ω]
    exact (map_ne_zero (algebraMap ℚ Ω)).2 (by simpa using hc0)
  have hQ'A : Polynomial.aeval a Q.primPart = 0 := by
    apply Subtype.ext
    change ((Polynomial.aeval a Q.primPart : A) : Ω) = (0 : Ω)
    rw [← hQ'Ω]
    exact (Polynomial.aeval_algHom_apply A.subtype.toIntAlgHom a Q.primPart).symm
  obtain ⟨i, hi⟩ : ∃ i, ¬ (l : ℤ) ∣ Q.primPart.coeff i := by
    by_contra hall
    push_neg at hall
    have hd : Polynomial.C (l : ℤ) ∣ Q.primPart := Polynomial.C_dvd_iff_dvd_coeff _ _ |>.2 hall
    have hu := Polynomial.isPrimitive_primPart Q _ hd
    rw [Int.isUnit_iff] at hu
    have := hp.out.two_le
    omega
  set Q2 := Q.primPart.map (Int.castRingHom (ZMod l))
  have hQ2 : Q2 ≠ 0 := by
    intro h
    have := congrArg (fun p => Polynomial.coeff p i) h
    simp only [Q2, Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at this
    exact hi ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this)
  have hev : Polynomial.aeval (IsLocalRing.residue A a) Q2 = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, RingHom.ext_int ((algebraMap (ZMod l) _).comp (Int.castRingHom _)) (algebraMap ℤ _), ← Polynomial.aeval_def]
    exact (Polynomial.aeval_algHom_apply (IsLocalRing.residue A).toIntAlgHom a Q.primPart).trans (by
      change IsLocalRing.residue A (Polynomial.aeval a Q.primPart) = 0
      rw [hQ'A, map_zero])
  have hint : IsIntegral (ZMod l) (IsLocalRing.residue A a) := IsAlgebraic.isIntegral (⟨Q2, hQ2, hev⟩ : IsAlgebraic (ZMod l) (IsLocalRing.residue A a))
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) := Module.finite_of_finite (ZMod l)
  letI := Fintype.ofFinite (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a})
  refine ⟨Fintype.card (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}), Fintype.one_lt_card, ?_, ?_⟩
  · have h0 := FiniteField.cast_card_eq_zero (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a})
    have h1 : ((Fintype.card (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) : ℕ) : IsLocalRing.ResidueField A) = 0 := by
      have := congrArg (algebraMap (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}) (IsLocalRing.ResidueField A)) h0
      rwa [map_natCast, map_zero] at this
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff] at h1
    simpa using h1
  · have h0 := FiniteField.pow_card (⟨IsLocalRing.residue A a, IntermediateField.mem_adjoin_simple_self _ _⟩ : (IntermediateField.adjoin (ZMod l) {IsLocalRing.residue A a}))
    have h1 := congrArg Subtype.val h0
    simp only [IntermediateField.coe_pow] at h1
    rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff] at h1
    simpa using h1

private theorem exists_r0_valuation_sub_lt_one_of_isAlgebraic {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) {l : ℕ} [Fact l.Prime] (hl : A.valuation (l : Ω) < 1) (a : A) (halg : IsAlgebraic ℚ (a : Ω)) :
    ∃ w ∈ R0 A, A.valuation (w - a) < 1 := by
  obtain ⟨q, hq2, hq, haq⟩ := fin_lemma_3 A hl a halg
  set T : Polynomial Ω := Polynomial.X ^ q - Polynomial.X with hT
  have hTm : T.Monic := Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast (by omega : 1 < q))
  have hprod := (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hTm (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits T))).symm
  have hroot : ∀ w ∈ T.roots, w ^ q = w := by
    intro w hw
    have := (Polynomial.mem_roots hTm.ne_zero).1 hw
    simpa [T, sub_eq_zero] using this
  have hev : T.eval (a : Ω) = (T.roots.map fun w => (a : Ω) - w).prod := by
    conv_lhs => rw [hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hv : A.valuation (T.eval (a : Ω)) < 1 := by simpa [T] using haq
  rw [hev, map_multiset_prod, Multiset.map_map] at hv
  obtain ⟨w, hw, hwv⟩ : ∃ w ∈ T.roots, A.valuation ((a : Ω) - w) < 1 := by
    by_contra hno
    push_neg at hno
    have h1 : (T.roots.map (A.valuation ∘ fun w => (a : Ω) - w)).prod = 1 := by
      apply Multiset.prod_eq_one
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
      refine le_antisymm ?_ (hno w hw)
      exact (A.valuation_le_one_iff _).2 (A.sub_mem a.2 (zero_one_mem_gammaSet_one A hq2 (hroot w hw)))
    rw [h1] at hv
    exact lt_irrefl _ hv
  have hwA : w ∈ A := zero_one_mem_gammaSet_one A hq2 (hroot w hw)
  refine ⟨w, ⟨hwA, fun s hs => ?_⟩, ?_⟩
  · have hsq : (s w) ^ q = s w := by rw [← map_pow, hroot w hw]
    change s ∈ Inertia A at hs
    unfold Inertia at hs
    exact eq_of_pow_eq_self_of_valuation_sub_lt_one A hq (zero_one_mem_gammaSet_one A hq2 hsq) hwA hsq (hroot w hw) (hs.2 w ((A.valuation_le_one_iff _).2 hwA))
  · rw [Valuation.map_sub_swap]
    exact hwv

open Polynomial IsLocalRing in
theorem UpperTheory.Kd.C7.residue_field_teichmuller_lift_exists :
    UpperTheory.Kd.C7.FixedIntegersMonicHasRootModPrime := by
  intro l _ hl2 Ω _ _ _ A hA P hP hdeg
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl : A.valuation (l : Ω) < 1 := by
    obtain ⟨pl, hpl, hlpl⟩ := hA
    unfold IsPlaceOver at hpl
    have := (hpl (l : 𝓞 ℚ)).2 hlpl
    simpa using this
  set Pm := P.map (R0 A).subtype with hPm
  have hmon : Pm.Monic := hP.map _
  have hdeg' : Pm.natDegree = P.natDegree := Polynomial.natDegree_map_eq_of_injective Subtype.val_injective P
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root Pm (by
    rw [Polynomial.degree_eq_natDegree hmon.ne_zero, hdeg']
    exact_mod_cast hdeg.ne')
  have hcA : ∀ i, Pm.coeff i ∈ A := fun i => by
    rw [hPm, Polynomial.coeff_map]
    exact (P.coeff i).2.1
  have hαA : α ∈ A := by
    by_contra hn
    have hv1 : 1 < A.valuation α := by
      rw [← not_le, A.valuation_le_one_iff]
      exact hn
    have h0 : Pm.eval α = 0 := hα
    rw [hmon.as_sum, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum] at h0
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at h0
    have e : α ^ Pm.natDegree = -∑ i ∈ Finset.range Pm.natDegree, Pm.coeff i * α ^ i := eq_neg_of_add_eq_zero_left h0
    have hle : A.valuation (∑ i ∈ Finset.range Pm.natDegree, Pm.coeff i * α ^ i) ≤ A.valuation α ^ (Pm.natDegree - 1) := by
      apply Valuation.map_sum_le
      intro i hi
      rw [map_mul, map_pow]
      calc A.valuation (Pm.coeff i) * A.valuation α ^ i ≤ 1 * A.valuation α ^ i := by
            gcongr
            exact (A.valuation_le_one_iff _).2 (hcA i)
        _ = A.valuation α ^ i := one_mul _
        _ ≤ A.valuation α ^ (Pm.natDegree - 1) := by
            apply pow_le_pow_right₀ hv1.le
            have := Finset.mem_range.1 hi
            omega
    have := congrArg A.valuation e
    rw [Valuation.map_neg, map_pow] at this
    rw [← this] at hle
    have hlt : A.valuation α ^ (Pm.natDegree - 1) < A.valuation α ^ Pm.natDegree :=
      pow_lt_pow_right₀ hv1 (by omega)
    exact absurd hle (not_le.2 hlt)
  obtain ⟨w, hwR, hwv⟩ := exists_r0_valuation_sub_lt_one_of_isAlgebraic A hl ⟨α, hαA⟩ (Algebra.IsAlgebraic.isAlgebraic α)
  refine ⟨⟨w, hwR⟩, ?_⟩
  by_contra hnot
  obtain ⟨u, hu⟩ := inertia_invariant_valuation_uniformizer_bound l hl2 Ω A hA _ hnot
  have hsub : R0 A ≤ A.toSubring := fun x hx => hx.1
  set φ := Subring.inclusion hsub
  set PA := P.map φ
  have hcoe : ∀ y : A.toSubring, ((PA.eval y : A.toSubring) : Ω) = Pm.eval (y : Ω) := by
    intro y
    have : Pm = PA.map A.toSubring.subtype := by
      rw [hPm, Polynomial.map_map]
      rfl
    rw [this, Polynomial.eval_map (p := PA)]
    exact (Polynomial.eval₂_hom (p := PA) A.toSubring.subtype y).symm
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub (⟨w, hwR.1⟩ : A.toSubring) ⟨α, hαA⟩ PA
  have hPw : ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) = (w - α) * (c : Ω) := by
    have h1 : ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) = Pm.eval w := by
      rw [hPm, Polynomial.eval_map]
      exact (Polynomial.eval₂_hom (R0 A).subtype _).symm
    have h2 := congrArg (fun z : A.toSubring => (z : Ω)) hc
    push_cast [hcoe] at h2
    rw [h1, ← sub_zero (Pm.eval w), ← (show Pm.eval α = 0 from hα)]
    exact h2
  have hsmall : A.valuation ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) < 1 := by
    rw [hPw, map_mul]
    calc A.valuation (w - α) * A.valuation (c : Ω) ≤ A.valuation (w - α) * 1 := by
          gcongr
          exact (A.valuation_le_one_iff _).2 c.2
      _ = A.valuation (w - α) := mul_one _
      _ < 1 := hwv
  have hinv : ((u : R0 A) : Ω) * ((u⁻¹ : (R0 A)ˣ) : R0 A) = 1 := by
    rw [← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]
  have hv2 := congrArg A.valuation hinv
  rw [map_mul, map_one, hu] at hv2
  have hle1 : A.valuation (((u⁻¹ : (R0 A)ˣ) : R0 A) : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 ((u⁻¹ : (R0 A)ˣ) : R0 A).2.1
  have : A.valuation ((Polynomial.eval (⟨w, hwR⟩ : R0 A) P : R0 A) : Ω) * A.valuation (((u⁻¹ : (R0 A)ˣ) : R0 A) : Ω) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' hle1) hsmall
  rw [hv2] at this
  exact lt_irrefl _ this

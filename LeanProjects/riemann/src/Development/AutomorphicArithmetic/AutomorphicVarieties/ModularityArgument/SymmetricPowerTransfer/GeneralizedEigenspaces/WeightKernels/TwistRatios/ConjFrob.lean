import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise in
private theorem cf_stab {H Ω : Type} [Field Ω] [Group H] [MulSemiringAction H Ω] (g : H) (B : ValuationSubring Ω)
    (h : ∀ y : Ω, g • y ∈ B ↔ y ∈ B) : g • B = B := by
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have key := h (g⁻¹ • y)
  simp only [smul_inv_smul] at key
  exact key.symm

private theorem cf_on {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {c : G (maximalRealSubfield L) Ω} (hc : IsConjEl c) (x : L) :
    c (algebraMap L Ω x) = algebraMap L Ω (IsCMField.complexConj L x) := by
  obtain ⟨j, hj⟩ := hc
  apply j.injective
  rw [hj]
  exact (IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) x).symm

private theorem cf_on_inv {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {c : G (maximalRealSubfield L) Ω} (hc : IsConjEl c) (x : L) :
    c.symm (algebraMap L Ω x) = algebraMap L Ω (IsCMField.complexConj L x) := by
  obtain ⟨j, hj⟩ := hc
  apply j.injective
  have h := IsCMField.complexEmbedding_complexConj L (j.comp (algebraMap L Ω)) x
  simp only [RingHom.comp_apply] at h
  have h2 := hj (c.symm (algebraMap L Ω x))
  simp only [AlgEquiv.apply_symm_apply] at h2
  rw [h, h2, Complex.conj_conj]

private theorem cf_primes {L : Type} [Field L] [NumberField L] [IsCMField L] (w w' : Plc L)
    (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    w' = w ∨ ∀ x : 𝓞 L, x ∈ w'.asIdeal ↔ IsCMField.ringOfIntegersComplexConj L x ∈ w.asIdeal := by
  unfold Plc at w w'
  unfold Lp at h
  have h' : w.asIdeal.under (𝓞 (maximalRealSubfield L)) = w'.asIdeal.under (𝓞 (maximalRealSubfield L)) := by
    rw [← HeightOneSpectrum.under_asIdeal, ← HeightOneSpectrum.under_asIdeal, h]
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 (maximalRealSubfield L)) (𝓞 L)
    (L ≃ₐ[maximalRealSubfield L] L) w.asIdeal w'.asIdeal h'
  have hmem : g ∈ Subgroup.zpowers (IsCMField.complexConj L) := by
    rw [IsCMField.zpowers_complexConj_eq_top]
    trivial
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [← zpow_mod_orderOf, IsCMField.orderOf_complexConj] at hg
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [Nat.cast_ofNat, hk, zpow_zero, one_smul] at hg
    exact HeightOneSpectrum.ext hg
  · right
    intro x
    rw [Nat.cast_ofNat, hk, zpow_one] at hg
    rw [hg, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have hinv : (IsCMField.complexConj L)⁻¹ = IsCMField.complexConj L := by
      apply inv_eq_of_mul_eq_one_right
      ext y
      simp
    have hx : (IsCMField.complexConj L)⁻¹ • x = IsCMField.ringOfIntegersComplexConj L x := by
      rw [hinv]
      ext
      simp
      rfl
    rw [hx]

open scoped Pointwise in
theorem UpperTheory.V.Z.Sym.Ga.conjFrob :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (c : G (maximalRealSubfield L) Ω), IsConjEl c → ∀ w w' : Plc L, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) → ∀ s, Ga.FrobAt w s → Ga.FrobAt w' s ∨ ∃ s', Ga.FrobAt w' s' ∧ s'.restrictScalars (maximalRealSubfield L) = c * s.restrictScalars (maximalRealSubfield L) * c⁻¹ := by
  intro L Ω _ _ _ _ _ _ c hc w w' hw s hs
  rcases cf_primes w w' hw with rfl | hx
  · exact Or.inl hs
  right
  unfold Ga.FrobAt at hs
  obtain ⟨A, hA, hF⟩ := hs
  unfold IsFrob at hF
  obtain ⟨hdec, hfr⟩ := hF
  let e : 𝓞 L ≃+* 𝓞 L := (IsCMField.ringOfIntegersComplexConj L).toRingEquiv
  have hq : normV w' = normV w := by
    unfold normV
    refine Nat.card_congr (Ideal.quotientEquiv w'.asIdeal w.asIdeal e ?_).toEquiv
    rw [Ideal.map_comap_of_equiv]
    ext y
    rw [Ideal.mem_comap, hx]
    simp [e]
  have hsA : ∀ z : Ω, s z ∈ A ↔ z ∈ A := by
    intro z
    have hstab : s • A = A := MulAction.mem_stabilizer_iff.mp hdec
    nth_rewrite 1 [← hstab]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  let A' : ValuationSubring Ω := A.comap (c.symm : Ω ≃+* Ω).toRingHom
  have hmem : ∀ y : Ω, (c : Ω ≃+* Ω) y ∈ A' ↔ y ∈ A := by
    intro y
    simp [A', ValuationSubring.mem_comap]
  let t : Ω ≃ₐ[maximalRealSubfield L] Ω := c * s.restrictScalars (maximalRealSubfield L) * c⁻¹
  have hfix : ∀ x : L, t.toRingEquiv (algebraMap L Ω x) = algebraMap L Ω x := by
    intro x
    change c (s (c⁻¹ (algebraMap L Ω x))) = algebraMap L Ω x
    rw [AlgEquiv.aut_inv, cf_on_inv hc, AlgEquiv.commutes, cf_on hc, IsCMField.complexConj_apply_apply]
  let s' : G L Ω := AlgEquiv.ofRingEquiv (f := t.toRingEquiv) hfix
  have hs' : ∀ y, s' y = c (s (c.symm y)) := by
    intro y
    rfl
  refine ⟨s', ?_, ?_⟩
  · unfold Ga.FrobAt
    refine ⟨A', ?_, ?_⟩
    · unfold IsPlaceOver
      intro x
      rw [hx x, ← hA]
      have hcx : algebraMap L Ω x = (c : Ω ≃+* Ω) (algebraMap L Ω (IsCMField.ringOfIntegersComplexConj L x)) := by
        change algebraMap L Ω x = c (algebraMap L Ω (IsCMField.complexConj L x))
        rw [cf_on hc, IsCMField.complexConj_apply_apply]
      rw [hcx]
      exact val_lt_one hmem _
    · rw [hq]
      unfold IsFrob
      constructor
      · apply MulAction.mem_stabilizer_iff.mpr
        apply cf_stab
        intro y
        rw [AlgEquiv.smul_def, hs']
        change c.symm (c (s (c.symm y))) ∈ A ↔ c.symm y ∈ A
        rw [AlgEquiv.symm_apply_apply, hsA]
      · intro y hy
        rw [ValuationSubring.valuation_le_one_iff] at hy
        have hz : c.symm y ∈ A := hy
        have hd : s' y - y ^ normV w = (c : Ω ≃+* Ω) (s (c.symm y) - (c.symm y) ^ normV w) := by
          rw [hs', map_sub, map_pow]
          change c (s (c.symm y)) - y ^ normV w = c (s (c.symm y)) - (c (c.symm y)) ^ normV w
          rw [AlgEquiv.apply_symm_apply]
        rw [hd, val_lt_one hmem]
        exact hfr _ ((ValuationSubring.valuation_le_one_iff _ _).mpr hz)
  · ext y
    rfl

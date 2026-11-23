import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

open ValuativeRel Topology

private theorem UpperTheory.V.Z.Tf.Orb.local_field_topology_facts (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] :
    T2Space E ∧ SecondCountableTopology E ∧ IsOpen {x : E | valuation E x ≤ 1} := by
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  letI : (Valued.v (R := E)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := E).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  refine ⟨inferInstance, ?_, Valued.isOpen_integer E⟩
  open scoped Valued in
  have : ProperSpace E := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace E
  infer_instance

theorem UpperTheory.V.Z.Tf.Orb.gLTop :
    UpperTheory.V.Z.Tf.Orb.GLTop := by
  intro E _ _ _ _ n
  obtain ⟨h2, hsc, hO⟩ := UpperTheory.V.Z.Tf.Orb.local_field_topology_facts E
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have hlast : ∀ Ω Ω' : Set (Matrix (Fin n) (Fin n) E), IsCompact Ω → IsCompact Ω' →
      IsCompact {g : GL (Fin n) E | (g : Matrix (Fin n) (Fin n) E) ∈ Ω ∧
        ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∈ Ω'} := by
    intro Ω Ω' hΩ hΩ'
    have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) E)).isCompact_preimage
      (hΩ.prod (hΩ'.image MulOpposite.continuous_op))
    have e : {g : GL (Fin n) E | (g : Matrix (Fin n) (Fin n) E) ∈ Ω ∧
        ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∈ Ω'} =
        Units.embedProduct (Matrix (Fin n) (Fin n) E) ⁻¹' (Ω ×ˢ (MulOpposite.op '' Ω')) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
        MulOpposite.op_injective.mem_set_image]
    rw [e]
    exact h
  refine ⟨Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology, inferInstance, ?_, hlast⟩
  let O : Subring E := (valuation E).integer
  let M : Set (Matrix (Fin n) (Fin n) E) := {A | ∀ i j, A i j ∈ O}
  have hMmul : ∀ A ∈ M, ∀ B ∈ M, A * B ∈ M := by
    intro A hA B hB i j
    rw [Matrix.mul_apply]
    exact O.sum_mem fun l _ => O.mul_mem (hA i l) (hB l j)
  have hMone : (1 : Matrix (Fin n) (Fin n) E) ∈ M := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  have hMo : IsOpen M := by
    have e : M = ⋂ i, ⋂ j, (fun A : Matrix (Fin n) (Fin n) E => A i j) ⁻¹' {x : E | valuation E x ≤ 1} := by
      ext A
      simp only [M, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hO.preimage (continuous_apply_apply i j)
  have hMc : IsCompact M := by
    have hc := IsNonarchimedeanLocalField.isCompact_closedBall E 1
    have h : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
        {x : E | valuation E x ≤ 1}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hc
    have e : M = (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
        {x : E | valuation E x ≤ 1}) := by
      ext A
      exact ⟨fun hA i _ j _ => hA i j, fun hA i j => hA i trivial j trivial⟩
    rw [e]
    exact h
  let K : Subgroup (GL (Fin n) E) :=
    { carrier := {g : GL (Fin n) E | (g : Matrix (Fin n) (Fin n) E) ∈ M ∧
        ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∈ M}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, ?_⟩
        · rw [Units.val_mul]
          exact hMmul _ ha _ hb
        · rw [mul_inv_rev, Units.val_mul]
          exact hMmul _ hb' _ ha'
      one_mem' := ⟨hMone, by rw [inv_one]; exact hMone⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨ha', by rw [inv_inv]; exact ha⟩ }
  refine ⟨K, ?_, hlast M M hMc hMc⟩
  exact (hMo.preimage Units.continuous_val).inter (hMo.preimage Units.continuous_coe_inv)

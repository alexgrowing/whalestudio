import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit

theorem UpperTheory.complex_conjugations_are_conjugate :
    UpperTheory.V.Sd.S2.ConjCc := by
  intro Ω _ _ _ a b ha hb
  obtain ⟨j, hj⟩ := ha
  obtain ⟨j', hj'⟩ := hb
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) j j'
    (Subsingleton.elim _ _)
  have h : ∀ x, j (σ.symm x) = j' x := fun x => by
    rw [← hσ]; rfl
  refine isConj_iff.2 ⟨σ, ?_⟩
  refine AlgEquiv.ext fun x => ?_
  apply j'.injective
  rw [hj', ← h, ← h]
  change j (σ.symm (σ (a (σ.symm x)))) = _
  rw [AlgEquiv.symm_apply_apply, hj]

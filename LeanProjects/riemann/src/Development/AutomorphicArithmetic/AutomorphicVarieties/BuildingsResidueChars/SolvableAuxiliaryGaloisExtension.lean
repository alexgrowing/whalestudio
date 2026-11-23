import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_auxiliary_galois_extension :
    UpperTheory.V.Af.Sol.ExistsCompositumWithPrimeDegreeGalois := by
  intro M Ω _ _ _ _ _ L _ _ _ hp hlt
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed M
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap M Ω).injective
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  have hαi : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  set P := minpoly ℚ α with hPdef
  have hPdeg : P.natDegree = Module.finrank ℚ L := by
    rw [← IntermediateField.adjoin.finrank hαi, hα, IntermediateField.finrank_top']
  let φ : L →ₐ[ℚ] Ω := IsAlgClosed.lift
  set β := φ α with hβdef
  have hβP : minpoly ℚ β = P := minpoly.algHom_eq φ φ.injective α
  set Q : Polynomial M := P.map (algebraMap ℚ M) with hQdef
  have hQ0 : Q ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hαi)
  have hsplit : (Q.map (algebraMap M Ω)).Splits := IsAlgClosed.splits _
  have hSF := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hsep : Q.Separable := Polynomial.Separable.map (Algebra.IsSeparable.isSeparable ℚ α)
  have hroot : ∀ y : Ω, y ∈ Q.rootSet Ω ↔ y ∈ P.rootSet Ω := by
    intro y
    rw [Polynomial.mem_rootSet, Polynomial.mem_rootSet, hQdef, Polynomial.aeval_map_algebraMap]
    exact and_congr_left fun _ => ⟨fun _ => minpoly.ne_zero hαi, fun _ => hQ0⟩
  have hβroot : β ∈ P.rootSet Ω := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hαi, hβP ▸ minpoly.aeval ℚ β⟩
  have hrange : ∀ x : L, φ x ∈ IntermediateField.adjoin M {β} := by
    intro x
    have h1 : φ x ∈ (⊤ : IntermediateField ℚ L).map φ := ⟨x, trivial, rfl⟩
    rw [← hα, IntermediateField.adjoin_map, Set.image_singleton] at h1
    have h2 : IntermediateField.adjoin ℚ {φ α} ≤ (IntermediateField.adjoin M {β}).restrictScalars ℚ :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.mem_adjoin_simple_self M β)
    exact h2 h1
  have hPs : (P.map (algebraMap ℚ L)).Splits := Normal.splits inferInstance α
  have hroots : ∀ y ∈ P.rootSet Ω, y ∈ Set.range φ := by
    intro y hy
    rw [← hPs.image_rootSet φ] at hy
    obtain ⟨x, -, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have heq : IntermediateField.adjoin M (Q.rootSet Ω) = IntermediateField.adjoin M {β} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := hroots y ((hroot y).1 hy)
      exact hrange x
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin M _ ((hroot β).2 hβroot)
  have hgal0 : IsGalois M (IntermediateField.adjoin M (Q.rootSet Ω)) := by
    haveI := hSF
    exact IsGalois.of_separable_splitting_field hsep
  have hgal : IsGalois M (IntermediateField.adjoin M {β}) := heq ▸ hgal0
  have hβQ : IsIntegral ℚ β := hαi.map φ
  have hβM : IsIntegral M β := hβQ.tower_top
  haveI hfdM : FiniteDimensional M (IntermediateField.adjoin M {β}) :=
    IntermediateField.adjoin.finiteDimensional hβM
  haveI hfdQ : FiniteDimensional ℚ (IntermediateField.adjoin M {β}) :=
    Module.Finite.trans M (IntermediateField.adjoin M {β})
  haveI hnf : NumberField (IntermediateField.adjoin M {β}) := {}
  let f : L →+* IntermediateField.adjoin M {β} := (φ : L →+* Ω).codRestrict _ hrange
  have hfin : Module.finrank M (IntermediateField.adjoin M {β}) = (minpoly M β).natDegree :=
    IntermediateField.adjoin.finrank hβM
  have hle : (minpoly M β).natDegree ≤ Module.finrank ℚ L := by
    rw [← hPdeg, ← Polynomial.natDegree_map (algebraMap ℚ M) (p := P)]
    refine Polynomial.natDegree_le_of_dvd ?_ hQ0
    have h4 := minpoly.dvd_map_of_isScalarTower ℚ M β
    rwa [hβP] at h4
  have hx : minpoly ℚ (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}) = P := by
    rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ (IntermediateField.adjoin M {β}) Ω)
      (algebraMap (IntermediateField.adjoin M {β}) Ω).injective]
    exact hβP
  have hdvd : Module.finrank ℚ L ∣ Module.finrank ℚ (IntermediateField.adjoin M {β}) := by
    have h5 := minpoly.degree_dvd (Algebra.IsIntegral.isIntegral (R := ℚ)
      (⟨β, IntermediateField.mem_adjoin_simple_self M β⟩ : IntermediateField.adjoin M {β}))
    rwa [hx, hPdeg] at h5
  have hMpos : 0 < Module.finrank ℚ M := Module.finrank_pos
  have hEpos : 0 < Module.finrank M (IntermediateField.adjoin M {β}) := Module.finrank_pos
  have hdeg : Module.finrank M (IntermediateField.adjoin M {β}) = Module.finrank ℚ L := by
    rw [← Module.finrank_mul_finrank ℚ M (IntermediateField.adjoin M {β})] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
    · exact absurd h3 (Nat.not_dvd_of_pos_of_lt hMpos hlt)
    · exact le_antisymm (hfin ▸ hle) (Nat.le_of_dvd hEpos h3)
  have htop : Algebra.adjoin M (Set.range f) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : (z : Ω) ∈ Algebra.adjoin M {β} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hβM.isAlgebraic]
      exact z.2
    have hsub : Algebra.adjoin M {β} ≤
        (Algebra.adjoin M (Set.range f)).map (IntermediateField.adjoin M {β}).val := by
      rw [AlgHom.map_adjoin]
      apply Algebra.adjoin_mono
      rintro _ rfl
      exact ⟨f α, ⟨α, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hsub hz
    have hwz' : w = z := Subtype.ext hwz
    exact hwz' ▸ hw
  exact ⟨IntermediateField.adjoin M {β}, inferInstance, hnf, inferInstance, inferInstance,
    inferInstance, f, hgal, hdeg, htop⟩

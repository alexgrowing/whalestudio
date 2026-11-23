import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.finiteCharacter_of_algebraic_cyclotomic :
    UpperTheory.V.Af.AlgOfCyc → UpperTheory.V.Af.Sol.FinChar := by
  intro hA
  refine ⟨?_, ?_⟩
  · intro F Ω _ _ _ _ _ l _ ι δ hopen
    obtain ⟨h1, -, -⟩ := hA F Ω l ι
    have hcont : Continuous δ := by
      refine continuous_of_continuousAt_one δ ?_
      refine tendsto_nhds_of_eventually_eq ?_
      filter_upwards [hopen.mem_nhds (Subgroup.one_mem _)] with x hx
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
      rw [hx, map_one]
    haveI : Finite (Formalism.ConjugateSelfDual.G F Ω ⧸ δ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
    haveI : δ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    refine h1 δ hcont fun w _ => ?_
    obtain ⟨A, hAw⟩ := exists_isPlaceOver Ω w
    refine ⟨A, hAw, 0, δ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun s _ => ?_⟩
    rw [neg_zero, zpow_zero, mul_one, ← map_pow]
    exact Subgroup.pow_index_mem δ.ker s
  · intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ δ hδ
    let E : IntermediateField K Ω := (IsScalarTower.toAlgHom K M Ω).fieldRange
    haveI : FiniteDimensional K M := Module.Finite.of_restrictScalars_finite ℚ K M
    haveI : FiniteDimensional K E :=
      LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M Ω)).toLinearEquiv
    refine Subgroup.isOpen_mono ?_ E.fixingSubgroup_isOpen
    intro g hg
    have hfix : ∀ m : M, g (algebraMap M Ω m) = algebraMap M Ω m := by
      intro m
      exact (IntermediateField.mem_fixingSubgroup_iff E g).mp hg _ ⟨m, rfl⟩
    let g' : Formalism.ConjugateSelfDual.G M Ω := { g.toRingEquiv with commutes' := hfix }
    have hres : UpperTheory.V.Af.resG K M Ω g' = g := by
      ext x; rfl
    rw [MonoidHom.mem_ker, ← hres, ← MonoidHom.comp_apply, hδ, MonoidHom.one_apply]

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.sumCl_holds :
    UpperTheory.Gal.KunnethLefschetz.SumCl := by
  intro X r Y j hj s
  obtain ⟨hop, hcov, hdis⟩ := hj
  haveI := hop s
  apply AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion
  have hc : (Set.range (j s).base)ᶜ = ⋃ t ∈ {t : Fin r | t ≠ s}, Set.range (j t).base := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := hcov x
      refine ⟨t, ?_, ht⟩
      rintro rfl
      exact hx ht
    · rintro ⟨t, hts, ht⟩ hx
      exact Set.disjoint_left.mp (hdis t s hts) ht hx
  rw [← isOpen_compl_iff, hc]
  refine isOpen_biUnion fun t _ => ?_
  haveI := hop t
  exact (j t).isOpenEmbedding.isOpen_range

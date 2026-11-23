import Development.EtaleCohomology.TateTwists.TPairAssocPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem t_pa_cpush_htpy_of : t_pa_cpush_htpy := by
  intro R _ E I J u u' H n x
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
  show CohomologyClass.mk (zcomp α (Cocycle.ofHom u) (add_zero n)) =
    CohomologyClass.mk (zcomp α (Cocycle.ofHom u') (add_zero n))
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨α.1.comp (Cochain.ofHomotopy H) (show n + -1 = n - 1 by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), δ_ofHomotopy, Cocycle.δ_eq_zero]
  simp [zcomp, Cochain.comp_sub]

end LateralTheory.EtaleFoundations

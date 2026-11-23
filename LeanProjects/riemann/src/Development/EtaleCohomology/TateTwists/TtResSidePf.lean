import Development.EtaleCohomology.TateTwists.EtaleTensorTwistedResolutionOfExistenceBoundAndS

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tensor_universal_property : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u

def tensor_quasi_isomorphism : Prop :=
  ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u

theorem tt_res_side_of (huniv : tensor_universal_property) (hqis : tensor_quasi_isomorphism) : tt_res_side := by
  intro q _ i I J M T e hI hJ hflat σ τ hσ hτ
  obtain ⟨hIge, ε, hε, hgen⟩ := hI
  obtain ⟨u, hu, -⟩ := (huniv (ZMod q) σ hσ).1 τ ε (𝟙 J)
  have := hIge
  have := hJ
  refine ⟨u, hqis (ZMod q) σ τ hσ hτ hflat ε u hu, fun U ζ b => ?_⟩
  rw [hu U 0 0 0 (add_zero 0), hgen U ζ]
  simp only [HomologicalComplex.id_f]
  rfl

end LateralTheory.EtaleFoundations

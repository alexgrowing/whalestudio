import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Descent

theorem mem_of_includeRight_mem_map :
  ∀ (O O' R : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O'] [Module.Free O O'] [CommRing R] [Algebra O R] (I : Ideal R) (x : R), (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) x ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I → x ∈ I := by
  intro O O' R _ _ _ _ _ _ _ I x hx
  have hnt : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton O' (Module.subsingleton O O')
  have : Module.FaithfullyFlat O O' := inferInstance
  have : Module.FaithfullyFlat R (R ⊗[O] O') := inferInstance
  let c : O' ⊗[O] R ≃ₐ[O] R ⊗[O] O' := Algebra.TensorProduct.comm O O' R
  have hc : ∀ y : R, c (Algebra.TensorProduct.includeRight y) = algebraMap R (R ⊗[O] O') y := by
    intro y
    simp [c, Algebra.TensorProduct.algebraMap_apply]
  have hle : Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) I ≤
      Ideal.comap c (Ideal.map (algebraMap R (R ⊗[O] O')) I) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    simp only [Ideal.mem_comap]
    rw [hc]
    exact Ideal.mem_map_of_mem _ hy
  have h1 : algebraMap R (R ⊗[O] O') x ∈ Ideal.map (algebraMap R (R ⊗[O] O')) I := by
    have h2 := hle hx
    simp only [Ideal.mem_comap] at h2
    rwa [hc] at h2
  have h4 := Ideal.comap_map_eq_self_of_faithfullyFlat (B := R ⊗[O] O') I
  rw [← h4]
  exact h1

end GlobalTheory.CompanionTheory.Descent

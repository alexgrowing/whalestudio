import Mathlib
open scoped TensorProduct

namespace GlobalTheory

theorem exists_finite_separable_point_of_separableClosure_point :
    ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B →
      Nonempty (B →ₐ[k] SeparableClosure k) →
      ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'),
        FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  intro k B _ _ _ hB ⟨φ⟩
  classical
  obtain ⟨t, ht⟩ := hB.out
  let K : IntermediateField k (SeparableClosure k) :=
    IntermediateField.adjoin k (φ '' (t : Set B))
  have hfin : (φ '' (t : Set B)).Finite := t.finite_toSet.image φ
  haveI : Finite (φ '' (t : Set B)) := hfin.to_subtype
  have hfd : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsSeparable.isSeparable k x).isIntegral)
  have hsep : Algebra.IsSeparable k K := Algebra.IsSeparable.of_algHom k (SeparableClosure k) K.val
  have hmem : ∀ b, φ b ∈ K.toSubalgebra := by
    intro b
    apply IntermediateField.algebra_adjoin_le_adjoin
    rw [← AlgHom.map_adjoin, ht]
    exact ⟨b, trivial, rfl⟩
  exact ⟨K, inferInstance, inferInstance, hfd, hsep, ⟨φ.codRestrict K.toSubalgebra hmem⟩⟩

end GlobalTheory

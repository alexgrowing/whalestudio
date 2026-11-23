import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem UpperTheory.quantum_determinant_map {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

theorem UpperTheory.algMod_of_injective_intertwining :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (f : M →ₗ[ℂ] N) (E : Fin n → Fin n → Module.End ℂ M) (E' : Fin n → Fin n → Module.End ℂ N), (∀ i j x, f (E i j x) = E' i j (f x)) → ∀ u x, f (Formalism.REAL.qdet E u x) = Formalism.REAL.qdet E' u (f x) := by
  intro M _ _ N _ _ n f E E' h u x
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ N) :=
    { carrier := {p | ∀ y, f (p.1 y) = p.2 (f y)}
      mul_mem' := fun {a b} ha hb y => (ha _).trans (congrArg a.2 (hb y))
      add_mem' := fun {a b} ha hb y => by
        simp only [Prod.fst_add, Prod.snd_add, LinearMap.add_apply, map_add, ha y, hb y]
      algebraMap_mem' := fun c y => map_smul f c y }
  let Z : Fin n → Fin n → S := fun i j => ⟨(E i j, E' i j), h i j⟩
  have h1 : (Formalism.REAL.qdet Z u).1.1 = Formalism.REAL.qdet E u :=
    UpperTheory.quantum_determinant_map ((AlgHom.fst ℂ _ _).comp S.val) Z u
  have h2 : (Formalism.REAL.qdet Z u).1.2 = Formalism.REAL.qdet E' u :=
    UpperTheory.quantum_determinant_map ((AlgHom.snd ℂ _ _).comp S.val) Z u
  rw [← h1, ← h2]
  exact (Formalism.REAL.qdet Z u).2 x

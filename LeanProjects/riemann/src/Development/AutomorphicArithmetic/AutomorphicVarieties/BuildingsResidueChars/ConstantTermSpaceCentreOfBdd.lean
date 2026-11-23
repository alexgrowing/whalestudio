import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConstantTermLinearMapEquivariantUniversalE
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTermSpace_centre_of_bdd :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → Centre (ctSp r S) := by
  intro K _ _ n r S hS z hz
  obtain ⟨p, hp, hpS⟩ := hS.centre z hz
  obtain ⟨f, hf, hfu⟩ := UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping K n r
  refine ⟨p, hp, fun x hx => ?_⟩
  have hle : ctSp r S ≤ LinearMap.ker (Polynomial.aeval (uAction z : Module.End ℂ (archSmooth K n)) p) := by
    refine Submodule.span_le.2 ?_
    rintro ψ ⟨φ, hφ, hψ⟩
    have hA : φ.1 ∈ automorphicForms K n := mem_automorphicForms.2 (UpperTheory.isAutomorphicForm_of_bdd_submodule K n S hS φ hφ)
    let incl : automorphicForms K n →ₗ[ℂ] archSmooth K n :=
      Submodule.inclusion automorphicForms_le_archSmooth
    have h1 := map_aeval_apply_of_intertwine incl (A := uActionAF K n z) (B := uAction z) (fun _ => rfl) p ⟨φ.1, hA⟩
    have h2 : Polynomial.aeval (uActionAF K n z) p ⟨φ.1, hA⟩ = 0 := by
      apply Submodule.inclusion_injective automorphicForms_le_archSmooth
      rw [map_zero]
      exact h1.trans ((Submodule.mem_bot ℂ).1 (hpS φ hφ))
    have h3 := map_aeval_apply_of_intertwine f (A := uActionAF K n z) (B := uAction z) (hfu z) p ⟨φ.1, hA⟩
    have h4 : ψ = f ⟨φ.1, hA⟩ := Subtype.ext (hψ.trans (hf ⟨φ.1, hA⟩).symm)
    refine LinearMap.mem_ker.2 ?_
    rw [h4, ← h3, h2, map_zero]
  exact (Submodule.mem_bot ℂ).2 (hle hx)

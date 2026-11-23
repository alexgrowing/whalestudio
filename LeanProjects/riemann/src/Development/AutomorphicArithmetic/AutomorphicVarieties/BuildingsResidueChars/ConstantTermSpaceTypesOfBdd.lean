import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocallyFiniteOfAlgModCriterion
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTermSpace_types_of_bdd :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → Types (ctSp r S) := by
  intro K _ _ n r S hS
  obtain ⟨V, hV, hst, hmem⟩ := hS.types
  refine ⟨V, hV, hst, fun ψ hψ g => ?_⟩
  unfold ctSp at hψ
  induction hψ using Submodule.span_induction with
  | mem ψ h =>
    obtain ⟨φ, hφ, he⟩ := h
    have hc : Continuous φ.1 := (UpperTheory.isAutomorphicForm_of_bdd_submodule K n S hS φ hφ).continuous
    rw [he]
    refine @UpperTheory.locallyFinite_of_algMod_criterion _ (archCompact K n) (_) _ V hV
      (fun X k => φ.1 (unipGL X * (g * infEmb K n k.1))) (fun X => ?_)
      (fun k => integrableOn_constantTerm hc _)
    simpa only [mul_assoc] using hmem φ hφ (unipGL X * g)
  | zero => exact V.zero_mem
  | add x y _ _ hx hy => exact V.add_mem hx hy
  | smul c x _ hx => exact V.smul_mem c hx

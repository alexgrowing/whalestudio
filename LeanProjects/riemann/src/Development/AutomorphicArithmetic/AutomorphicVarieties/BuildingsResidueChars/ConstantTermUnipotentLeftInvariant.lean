import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTerm_unipotent_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ), IsLeftInvariant φ → ∀ (X : UPos n r → AdeleRing (𝓞 K) K) g, constantTerm r φ (unipGL X * g) = constantTerm r φ g := by
  intro K _ _ n r φ hφ X g
  have hfd := isAddFundamentalDomain_unipFundamentalDomain (K := K) (n := n) (r := r)
  have hfd' := hfd.vadd_of_comm X
  rw [constantTerm_eq_setIntegral hφ hfd, constantTerm_eq_setIntegral hφ hfd' g, ← Set.image_vadd]
  simp only [vadd_eq_add]
  rw [(measurePreserving_add_left (unipMeasure K n r) X).setIntegral_image_emb
      (MeasurableEquiv.addLeft X).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  show φ (unipGL Y * (unipGL X * g)) = φ (unipGL (X + Y) * g)
  rw [add_comm X Y, unipGL_add, mul_assoc]

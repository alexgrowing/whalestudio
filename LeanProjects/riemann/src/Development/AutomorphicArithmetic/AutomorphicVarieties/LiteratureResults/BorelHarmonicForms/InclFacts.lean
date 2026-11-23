import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.inclFacts :
    UpperTheory.V.Lit.Bor.InclFacts := by
  intro E _ _ _ a π Ξ r
  have hA : ∀ X m, incl π Ξ (lieA π Ξ X m) = smA Ξ X (incl π Ξ m) := fun X m => by
    induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ v => rfl
  have hB : ∀ X m, incl π Ξ (lieB π Ξ X m) = smB Ξ X (incl π Ξ m) := fun X m => by
    rw [smB_apply]
    induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ v => rfl
  refine ⟨?_, fun i m => ?_, fun k m => ?_, fun X m => ?_, fun X m => ?_⟩
  · exact Module.Flat.rTensor_preserves_injective_linearMap _ π.V.injective_subtype
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
    | tmul φ v =>
      rw [cmp_tmul]
      exact cmp_tmul i φ.1 v
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ v => rfl
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ v => rfl
  · rw [piAdj, smAdj, adj_apply, adj_apply, map_sub, map_sub, hA, hB, LinearMap.map_smul_of_tower]

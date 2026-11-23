import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingPadicAlgClPlace
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.adicNorm_prod_le_prod_of_injective_classes :
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (O S R : Type) [Fintype O] [Fintype S] (f : O → S → ℂ), (∀ o s, IsIntegral ℤ (f o s)) → ∀ (X : O → Finset R) (cl : ∀ o, ↥(X o) → S), (∀ o, Function.Injective (cl o)) → ‖ι.symm (∏ o, ∏ s, f o s)‖ ≤ ∏ o, ∏ r : ↥(X o), ‖ι.symm (f o (cl o r))‖ := by
  intro l _ ι O S R _ _ f hf X cl hcl
  classical
  have h1 : ∀ o s, ‖ι.symm (f o s)‖ ≤ 1 := fun o s =>
    GlobalTheory.norm_le_one_of_isIntegral_int (map_isIntegral_int ι.symm (hf o s))
  rw [map_prod, norm_prod]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun o _ => ?_)
  rw [map_prod, norm_prod]
  have h2 : ∏ r : ↥(X o), ‖ι.symm (f o (cl o r))‖
      = ∏ s ∈ Finset.univ.map ⟨cl o, hcl o⟩, ‖ι.symm (f o s)‖ := by
    rw [Finset.prod_map]; rfl
  rw [h2]
  exact Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _)
    (fun _ _ => norm_nonneg _) (fun s _ _ => h1 o s)

import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.PetEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CuspSq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SmForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.InclFacts
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.piForm :
    UpperTheory.V.Lit.Bor.PiForm := by
  intro E _ _ _ a ha π Ξ r hone
  obtain ⟨G, hG⟩ := admEx E a Ξ
  obtain ⟨H, hH⟩ := petEx E a ha r
  obtain ⟨hinj, hcmp, -, hlie, hadj⟩ := inclFacts E a π Ξ r
  have hpos := tformPos _ Ξ.d H _ G hH.pos hG.pos
  have hmem : ∀ m, incl π Ξ m ∈ tens Ξ.d (sqSub E a r) := fun m =>
    mem_tens.2 fun i => by
      rw [hcmp]
      exact Submodule.subset_span (cuspSq E a ha π r hone _ (UpperTheory.V.Lit.Bor.cmp i m).2)
  refine ⟨((tform H G) ∘ₛₗ (incl π Ξ)).compl₂ (incl π Ξ), ⟨fun x y => ?_, fun x _ => ?_, fun x _ hx => ?_⟩,
    fun X x y => ?_⟩
  · exact hpos.herm _ _
  · exact hpos.nonneg _ (hmem x)
  · exact hinj ((hpos.definite _ (hmem x) hx).trans (map_zero _).symm)
  · show tform H G (incl π Ξ x) (incl π Ξ _) = tform H G (incl π Ξ _) (incl π Ξ y)
    rw [hlie, hadj]
    exact smForm E a Ξ r H G hH hG X _ (hmem x) _ (hmem y)

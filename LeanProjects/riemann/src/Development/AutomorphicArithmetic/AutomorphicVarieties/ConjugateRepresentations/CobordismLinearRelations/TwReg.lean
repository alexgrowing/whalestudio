import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.twReg :
    UpperTheory.V.Cj.TwReg := by
  intro E _ _ _ a n π μ m hμ hm hr ν hν; refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun t => ?_
  have e := ((hμ t).twist ν).infChar_eq
  rw [e, (InfType.expo_of_infType E ν).2.1 _ hν t]
  obtain ⟨-, h1, h2⟩ := hr t
  refine ⟨(Multiset.nodup_of_le (hm t) h1).map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := h2 y (Multiset.mem_of_le (hm t) hy)
  exact ⟨k, by push_cast; ring⟩

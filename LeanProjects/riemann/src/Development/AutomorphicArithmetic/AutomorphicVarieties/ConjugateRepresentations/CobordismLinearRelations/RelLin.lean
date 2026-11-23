import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ZigClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.LevSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.CobLin
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.relLin :
    UpperTheory.V.Cj.RelLin := by
  intro E _ _ _ a U σ Ξ Ξ' h q s α α' β β' ⟨a1, b1, c, d, p1, p2, p3⟩ ⟨a2, b2, c', d', r1, r2, r3⟩
  refine ⟨(levSub E a Ξ q).1 U s _ _ a1 a2, (levSub E a Ξ' q).1 U (σ s) _ _ b1 b2, s • c + c', σ s • d + d', ?_, ?_, ?_⟩
  · simpa only [one_smul] using (perEx E a U Ξ q).2.2 α α' c c' s 1 p1 r1
  · simpa only [one_smul] using (perEx E a U Ξ' q).2.2 β β' d d' (σ s) 1 p2 r2
  · have e : σ s • d + d' - sigC σ h (s • c + c') = σ s • (d - sigC σ h c) + (d' - sigC σ h c') := by
      funext z y i
      simp only [sigC, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
      ring
    rw [e]
    exact cobLin _ _ _ q (σ s) _ _ p3 r3

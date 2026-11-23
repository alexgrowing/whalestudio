import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.FnProj0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LocLimMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ChiGrow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevOfMulChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevMulChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SkewLieActionL2
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.fnProj :
    UpperTheory.V.Cj.H.FnProj := by
  intro E _ _ _ a ha r n e he c
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsHaarMeasure := inferInstanceAs (Measure.haar : Measure (GA E a)).IsHaarMeasure
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Lit.Bor.twEx E a ha r
  obtain ⟨P, Q, S, h⟩ := fnProj0 E a ha μ n e he c
  obtain ⟨P', Q', S', h'⟩ := twRes E a r χ hχ (gard μ) n e c P Q S h
  refine ⟨_, P', Q', S', ⟨fun X φ hφ => (twSq E a ha μ r χ hχ φ hφ).1 X, fun φ hφ => ?_,
    fun φ hφ => (twSq E a ha μ r χ hχ φ hφ).2, fun φ h1 h2 h3 h4 => twCpt E a ha μ r χ hχ φ h1 h2 h3 h4⟩, h'⟩
  obtain ⟨s, hs⟩ := hχ.1
  exact chiGrow E a χ s hs φ (gardFacts E a ha μ _ hφ).2.2.1

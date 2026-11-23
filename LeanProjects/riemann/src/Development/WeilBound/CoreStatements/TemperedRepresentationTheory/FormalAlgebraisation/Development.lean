import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismUniquenessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsoOfThickeningsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismExistenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosedProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalAlgebraisationSchemesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosedStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace PositivityTheory.FormalThickening

theorem formalAlgebraisation : GlobalTheory.Published.FormalAlgebraisation := by
  refine ⟨?_, GlobalTheory.T.formal_algebraisation_schemes GlobalTheory.T.grothendieck_existence_closed_proj⟩
  intro R _ _ I hI X Z hX hZs hZl hZq Y β b hb hβ f hf hfβ
  obtain ⟨g, hg⟩ := GlobalTheory.T.formal_morphism_existence GlobalTheory.T.grothendieck_existence_closed GlobalTheory.T.iso_of_thickenings R I hI X Z hX hZs hZl hZq Y β b hb hβ f hf hfβ
  refine ⟨g, hg, fun g' hg' => ?_⟩
  exact GlobalTheory.T.formal_morphism_uniqueness R I hI X Z hX hZs Y b hb g' g (fun e => (hg' e).trans (hg e).symm)

end PositivityTheory.FormalThickening

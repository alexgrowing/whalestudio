import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneFormMapEqKaehlerDifferentialMap
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FewEquationsStatementStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
open GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

theorem fewEquations_of_fewEqSt (hF : FewEqSt) (hLe : H1StructureDimLe) : FewEquations := by
  intro R _ _ _ A _ g hab hsm M hM I hI hJ
  refine hF R A.left A.hom g hab.smooth hab.proper ?_ M hM I hI hJ
  intro X' s' φ hP
  obtain ⟨_, hab', hsm'⟩ := GlobalTheory.CompanionTheory.Hodge.FormBC.exists_grp A g hab hsm s' φ hP
  exact hLe _ (Over.mk s') g hab' hsm'

theorem fewEquations_pf : H1StructureDimLe → FewEquations := fun hLe => fewEquations_of_fewEqSt GlobalTheory.T.FewEquationsStatement hLe

end CompanionTheory.PfDual

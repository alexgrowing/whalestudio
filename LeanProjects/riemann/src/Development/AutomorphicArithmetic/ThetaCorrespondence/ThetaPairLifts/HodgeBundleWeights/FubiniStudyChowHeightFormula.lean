import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.FubiniStudyChowHeight.FubiniStudyChowHeightOfArExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ProjSpace ChowFormHeightComparison₂.CF
attribute [local instance] MvPolynomial.gradedAlgebra
namespace FubiniStudyChowHeightFormula₂.Fs
variable (R : Type) [CommRing R] (N : ℕ)
end FubiniStudyChowHeightFormula₂.Fs
theorem FubiniStudyChowHeightFormula₂.fubiniStudy_chowHeight_formula (h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : GlobalTheory.Published.FubiniStudyChowHeight :=
  FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of h.p4
end
end

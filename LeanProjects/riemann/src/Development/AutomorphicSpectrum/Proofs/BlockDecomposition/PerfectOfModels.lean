import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfAllOfModels
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfGenericIsoStatement

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.SpreadingModels

theorem perfAll_of_hasModel
    (hModel : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
      ∀ M : LB Y, M.IsLB → HasModel f M) : PerfAll :=
  perfAll_of_models GlobalTheory.T.perfect_base_change GlobalTheory.T.perfect_of_generic_iso hModel

end GlobalTheory.CompanionTheory.SpreadingModels

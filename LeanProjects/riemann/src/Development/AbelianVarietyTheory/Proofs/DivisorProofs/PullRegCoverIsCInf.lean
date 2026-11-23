import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapEqOfMemPtsIn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

theorem VMetric.pull_regCover_isCInf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    [IsIntegral X] (E : X.Modules) (r : ℕ) (h : VMetric p E r), h.IsCInfNorm →
    ∀ C : RegCover p, (h.pull C.ρ rfl).IsCInf := fun k _ _ p _ _ _ _ H C =>
  H.pull_isCInf_of_local C.ρ (GlobalTheory.RegGenSmooth.genSmooth_of_isRegSurf k C.Y (C.ρ ≫ p) C.reg).2

end GlobalTheory

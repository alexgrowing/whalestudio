import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannDualFormIndep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCovEqMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfFst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjRiemannData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsDualRiemannOf

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory

theorem PPAS.exists_isDualRiemann : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (P : PPAS X) (t : ℝ), 0 < t → ∃ h : VMetric p (LieVB.omega P.A) P.g, P.IsDualRiemann t h :=
  PPAS.exists_isDualRiemann_of GlobalTheory.CovFactor.exists_cov_eq_mulVec GlobalTheory.UnifTangent.riemannData_tangent GlobalTheory.UnifImmersive.eq_zero_of_cov GlobalTheory.PPAS.exists_conj_riemannData
    GlobalTheory.RiemannExists.nonempty_riemannData GlobalTheory.RiemIndep.riemann_dual_form_indep

end GlobalTheory

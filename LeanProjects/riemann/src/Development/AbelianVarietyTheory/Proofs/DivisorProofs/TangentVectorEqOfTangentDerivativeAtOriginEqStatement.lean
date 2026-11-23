import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorEqOfTangentDerivativeAtOriginEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVector_eq_of_tangentDerivativeAtOrigin_eq : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (u v : TanM (𝟙 (Sp R)) G), (∀ f, tanDer G u f = tanDer G v f) → u = v := by
  first | exact @GlobalTheory.CoordsOrigin.tanM_eq_of_tanDer | exact GlobalTheory.CoordsOrigin.tanM_eq_of_tanDer | (intros; apply GlobalTheory.CoordsOrigin.tanM_eq_of_tanDer <;> assumption)

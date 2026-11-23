import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivativeAtOriginAddTangentVector
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
theorem _root_.GlobalTheory.T.tangentDerivativeAtOrigin_add_tangentVector : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (u v : TanM (𝟙 (Sp R)) G) (f : G.left.presheaf.stalk (origin G)), tanDer G (u + v) f = tanDer G u f + tanDer G v f := by
  first | exact @GlobalTheory.CoordsOrigin.tanDer_add | exact GlobalTheory.CoordsOrigin.tanDer_add | (intros; apply GlobalTheory.CoordsOrigin.tanDer_add <;> assumption)

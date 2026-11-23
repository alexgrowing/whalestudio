import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorOfOriginDerivation
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
theorem _root_.GlobalTheory.T.exists_tangentVector_of_originDerivation : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (D : G.left.presheaf.stalk (origin G) → R), (∀ x y, D (x + y) = D x + D y) → (∀ x y, D (x * y) = evO G x * D y + evO G y * D x) → (∀ r, D (constO G r) = 0) → ∃ v : TanM (𝟙 (Sp R)) G, ∀ f, tanDer G v f = D f := by
  first | exact @GlobalTheory.CoordsOrigin.exists_tan_of_derivation | exact GlobalTheory.CoordsOrigin.exists_tan_of_derivation | (intros; apply GlobalTheory.CoordsOrigin.exists_tan_of_derivation <;> assumption)

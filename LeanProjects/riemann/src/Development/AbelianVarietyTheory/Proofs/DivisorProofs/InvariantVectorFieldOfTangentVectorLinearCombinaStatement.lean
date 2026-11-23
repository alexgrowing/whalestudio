import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldOfTangentVectorLinearCombina
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_vectorField_of_tangent_vector_linear_combination : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g : ℕ) (w : Fin g → TanM (𝟙 (Sp R)) G) (e : Fin g → Fld G.left), (∀ c, IsInv G (w c) (e c)) → ∀ a : Fin g → R, IsInv G (∑ c, a c • w c) (fun O f => ∑ c, constFn G.hom O (a c) * e c O f) := by
  first | exact @GlobalTheory.Heat.InvComb.isInv_comb | exact GlobalTheory.Heat.InvComb.isInv_comb | (intros; apply GlobalTheory.Heat.InvComb.isInv_comb <;> assumption)

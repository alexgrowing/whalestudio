import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSignatureSumEqTwiceDimension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigRank
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
theorem _root_.GlobalTheory.T.cmType_signature_sum_eq_twice_dimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ), ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) * (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) = 2 * (Module.finrank ℚ E / 2 * p * q) := by
  first | exact @GlobalTheory.BalProj.signature_count | exact GlobalTheory.BalProj.signature_count | (intros; apply GlobalTheory.BalProj.signature_count <;> assumption)

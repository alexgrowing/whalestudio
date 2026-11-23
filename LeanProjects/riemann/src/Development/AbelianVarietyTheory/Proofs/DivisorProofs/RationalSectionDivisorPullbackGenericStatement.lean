import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_divisor_pullback_generic : ∀ (G Y : Scheme.{0}) [IsIntegral G] [IsIntegral Y] [IsLocallyNoetherian G] [IsLocallyNoetherian Y] (j : G ⟶ Y), j (genericPoint G) = genericPoint Y → (∀ x : G, IsIso (j.stalkMap x)) → ∀ (M : LB Y) (hM : M.IsLB) (r : M.ι → Y.functionFieldˣ) (hr : IsRatSec M r), ∃ (r' : (M.pull j).ι → G.functionFieldˣ) (hr' : IsRatSec (M.pull j) r'), ∀ x : G, (divOfRatSec (LB.isLB_pull hM j) hr').mult x = (divOfRatSec hM hr).mult (j x) := by
  first | exact @GlobalTheory.MultPull.exists_isRatSec_pull_mult | exact GlobalTheory.MultPull.exists_isRatSec_pull_mult | (intros; apply GlobalTheory.MultPull.exists_isRatSec_pull_mult <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreIntersectionFormula
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_intersection_formula : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] [IsLocallyNoetherian Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d e : ℕ), IsArithVar q d → IsArithVar p (d + (e + 1)) → ∀ (f : Y ⟶ B), f ≫ q = p → ∀ (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (L : Fin (e + 1) → LB Y) (hL : ∀ a, (L a).IsLB) (r : (L 0).ι → Y.functionFieldˣ) (hr : IsRatSec (L 0) r) (γ : Y → ℤ), (∀ z, (divOfRatSec (hL 0) hr).mult z ≠ 0 → ∃ (Z : Scheme.{0}) (i : Z ⟶ Y) (_ : IsClosedImmersion i) (_ : IsIntegral Z) (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), i (genericPoint Z) = z ∧ IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) ∧ γ z = (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a : Fin e => ((L a.succ).pull i).pull j'))) → (letI := algebraΓOfHom s; interNum B.functionField (structureModule G) (fun a => (L a).pull j)) = ∑ᶠ z, (divOfRatSec (hL 0) hr).mult z * γ z := by
  first | exact @GlobalTheory.GenFibreDegree.degree_genericFibre_ratSec | exact GlobalTheory.GenFibreDegree.degree_genericFibre_ratSec | (intros; apply GlobalTheory.GenFibreDegree.degree_genericFibre_ratSec <;> assumption)

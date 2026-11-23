import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreClosedSubvariety
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_closed_subvariety : ∀ (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (x : G) (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = j x → ∀ (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB Y), (∀ a, (P a).IsLB) → (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a => ((P a).pull i).pull j')) = (letI := algebraΓOfHom s; interNumRed B.functionField (⟨closure {x}, isClosed_closure⟩ : Closeds _) (fun a => (P a).pull j)) := by
  first | exact @GlobalTheory.FibreClosure.interNum_genericFibre_eq_interNumRed | exact GlobalTheory.FibreClosure.interNum_genericFibre_eq_interNumRed | (intros; apply GlobalTheory.FibreClosure.interNum_genericFibre_eq_interNumRed <;> assumption)

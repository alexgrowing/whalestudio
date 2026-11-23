import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialTopSelfIntersection
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_top_self_intersection : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (κ : Type) [Field κ] (Z : Scheme.{0}) [Algebra κ Γ(Z, ⊤)], IsProjOver (strHom κ Z) → ∀ (ι : Type) [Fintype ι] (D : ℕ), Fintype.card ι = D → topologicalKrullDim Z ≤ D → ∀ (i : Z ⟶ X) (N : ι → HermLB p), pol (fun n : ι → ℤ => (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ)) = D.factorial * (interNum κ (structureModule Z) (fun a => (N a).B.pull i) : ℝ) := by
  first | exact @GlobalTheory.FibreProj.pol_topSelf_comb_pull | exact GlobalTheory.FibreProj.pol_topSelf_comb_pull | (intros; apply GlobalTheory.FibreProj.pol_topSelf_comb_pull <;> assumption)

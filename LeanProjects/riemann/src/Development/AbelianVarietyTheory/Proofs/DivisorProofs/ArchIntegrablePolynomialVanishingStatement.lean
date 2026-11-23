import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrablePolynomialVanishing
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arch_integrable_polynomial_vanishing : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), GenSmooth q d → IsArithVar p D → ∀ (f : Y ⟶ B) (w : f ≫ q = p) (α β : Type) [Fintype α] [Fintype β], d < Fintype.card β → ∀ (L : α → HermLB p) (A : β → HermLB q) (M : HermLB p) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb (Sum.elim L fun a => (A a).pull f w) n).ArchIntegrable M D hr) → pol (fun n => (comb (Sum.elim L fun a => (A a).pull f w) n).archInt M D hr) = 0 := by
  first | exact @GlobalTheory.FibreProj.pol_archInt_pull_eq_zero | exact GlobalTheory.FibreProj.pol_archInt_pull_eq_zero | (intros; apply GlobalTheory.FibreProj.pol_archInt_pull_eq_zero <;> assumption)

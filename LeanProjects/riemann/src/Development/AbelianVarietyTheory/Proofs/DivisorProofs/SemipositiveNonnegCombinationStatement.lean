import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semipositive_nonneg_combination : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (ι : Type) [Fintype ι] (L : ι → GlobalTheory.HermLB p) (n : ι → ℤ) (D : ℕ), (∀ i, (L i).SemiPos D) → (∀ i, 0 ≤ n i) → (GlobalTheory.ArInt.comb L n).SemiPos D := by
  first | exact @GlobalTheory.ArInt.semiPos_comb | exact GlobalTheory.ArInt.semiPos_comb | (intros; apply GlobalTheory.ArInt.semiPos_comb <;> assumption)

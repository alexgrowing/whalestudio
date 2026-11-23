import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDegreeOfEulerChar
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_chern_degree_of_euler_char : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (G D : T.Modules) (r : ℕ), IsVB G r → Nonempty (D ≅ dual G) → ∀ (L : LB T), L.IsLB → ∀ c : ℚ, (∀ᶠ n in atTop, ((chi k (twist G (lbPow L n)) : ℚ) + (chi k (twist D (lbPow L n)) : ℚ)) / 2 - (r : ℚ) * (chi k (twist (structureModule T) (lbPow L n)) : ℚ) = c) → degCh2 k G = c := by
  first | exact @GlobalTheory.Div.degCh2_eq_of_eventually_twist | exact GlobalTheory.Div.degCh2_eq_of_eventually_twist | (intros; apply GlobalTheory.Div.degCh2_eq_of_eventually_twist <;> assumption)

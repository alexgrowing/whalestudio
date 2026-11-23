import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFunctionsPthPowerTwist
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.regular_functions_pth_power_twist : ∀ {X : Scheme.{0}} [IsIntegral X] (p : ℕ) (G H : CartierDiv X) (y : X), (H - p • G).Eff → {z : X.functionField | ∃ c ∈ {c : X.functionField | G.RegularAt y c}, ∃ b ∈ locRing y, z = c ^ p * b} ⊆ {c | H.RegularAt y c} := by
  first | exact @_root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt | exact _root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt | (intros; apply _root_.GlobalTheory.DI.pow_mul_locRing_subset_regularAt <;> assumption)

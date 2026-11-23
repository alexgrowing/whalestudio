import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaChernClassBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_chern_class_base_change : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ g₁ g : ℕ, g₁ ≤ g → ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k) [IsIntegral S], IsRegSurf p → ∀ P : PPAS S, P.g = g₁ → P.HasTheta → ∃ (k' : Type) (_ : CommRing k') (S' : Scheme.{0}) (p' : S' ⟶ Sp k') (_ : IsIntegral S') (P' : PPAS S') (n : ℕ), IsRegSurf p' ∧ P'.g = g ∧ P'.HasTheta ∧ 0 < n ∧ P'.degOmega p' = n * P.degOmega p ∧ ∀ a : ℝ, P.IsCh2Omega p a → P'.IsCh2Omega p' (n * a) := by
  first | exact @GlobalTheory.PPAS.exists_raise_dim_ch2Omega | exact GlobalTheory.PPAS.exists_raise_dim_ch2Omega | (intros; apply GlobalTheory.PPAS.exists_raise_dim_ch2Omega <;> assumption)

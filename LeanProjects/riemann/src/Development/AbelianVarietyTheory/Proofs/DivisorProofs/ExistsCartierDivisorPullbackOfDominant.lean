import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem exists_isPull : ∀ (Z V : Scheme.{0}) [IsIntegral Z] [IsIntegral V] (q : Z ⟶ V) [IsDominant q]
    (E : CartierDiv V), ∃ D : CartierDiv Z, IsPull q D E := by
  intro Z V _ _ q _ E
  obtain ⟨D, -, hD⟩ := exists_pullback_cartierDiv V Z q E
  exact ⟨D, fun y b hb x hx => hD x b (hx ▸ hb)⟩

end GlobalTheory.FlagPush

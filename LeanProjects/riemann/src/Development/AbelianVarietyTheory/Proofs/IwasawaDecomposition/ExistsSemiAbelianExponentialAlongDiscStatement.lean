import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDisc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semi_abelian_exponential_along_disc : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : ℂ → (Sp ℂ ⟶ X)) (r : ℝ), IsSemiAbelian G → 0 < r → IsHolTo (Metric.ball (0 : ℂ) r) y → ∃ (g : ℕ) (ρ : ℝ) (e : ∀ u, (Fin g → ℂ) → (Over.mk (y u) ⟶ G)), 0 < ρ ∧ ρ ≤ r ∧ IsHolTo (Metric.ball (0 : ℂ) ρ ×ˢ Set.univ) (fun q : ℂ × (Fin g → ℂ) => (show Sp ℂ ⟶ G.left from (e q.1 q.2).left)) ∧ (∀ u ∈ Metric.ball (0 : ℂ) ρ, (∀ z w, e u (z + w) = e u z * e u w) ∧ Function.Surjective (e u) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e u z).left)) ∧ (∀ w, ∃! v : epsPt (y u) ⟶ G, IsDerivAt0 (fun z => (e u z).left) w v.left) ∧ (∀ v : epsPt (y u) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e u 0).left → ∃! w, IsDerivAt0 (fun z => (e u z).left) w v.left)) ∧ ∀ z₀, e 0 z₀ = 1 → ∃ ζ : ℂ → (Fin g → ℂ), ζ 0 = z₀ ∧ AnalyticAt ℂ ζ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), e u (ζ u) = 1 := by
  first | exact @GlobalTheory.RelExp.exists_exp_along_disc | exact GlobalTheory.RelExp.exists_exp_along_disc | (intros; apply GlobalTheory.RelExp.exists_exp_along_disc <;> assumption)

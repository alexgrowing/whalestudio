import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2ExteriorSquareIso
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyper_h2_exterior_square_iso : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) → WedgeO F → (∀ a, cupHyp F a a = 0) → ∃ e : ⋀[R]^2 (Hyp1 F) ≃ₗ[R] Hyp2 F, ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = cupHyp F a b := by
  first | exact @GlobalTheory.AbCoh.exists_wedge_hyp_equiv | exact GlobalTheory.AbCoh.exists_wedge_hyp_equiv | (intros; apply GlobalTheory.AbCoh.exists_wedge_hyp_equiv <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralPullbackRationalSaturationModelOpen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.UPoinc GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_pullback_rationalSaturation_model_open : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R), (U₀ : Set M.Z).Nonempty → (∀ x : Sp Ω ⟶ U₀.toScheme, x ≫ U₀.ι = M.pt → x ≫ u₀ = spMap R.val.toRingHom) → IsIntegral (pullback u₀ (spMap (toRat R))) ∧ ∃ pt : Sp Ω ⟶ pullback u₀ (spMap (toRat R)), pt ≫ pullback.fst _ _ ≫ U₀.ι = M.pt ∧ Dense (Set.range pt) := by
  first | exact @GlobalTheory.UPoinc.isIntegral_pullback_toRat | exact GlobalTheory.UPoinc.isIntegral_pullback_toRat | (intros; apply GlobalTheory.UPoinc.isIntegral_pullback_toRat <;> assumption)

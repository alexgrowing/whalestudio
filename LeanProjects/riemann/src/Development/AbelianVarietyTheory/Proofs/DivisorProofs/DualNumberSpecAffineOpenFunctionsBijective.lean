import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructure

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB

namespace GlobalTheory.LieVB

theorem bijective_add_mul_epsFn : ∀ (O : Type) [CommRing O] (V : (Sp O).Opens), IsAffineOpen V → Function.Bijective (fun ab : Γ(Sp O, V) × Γ(Sp O, V) => (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.1 + (specO O (DualNumber O)).hom.appLE V ((specO O (DualNumber O)).hom ⁻¹ᵁ V) le_rfl ab.2 * resG _ le_top (epsFn O)) := by
  intro O _ V hV
  have H : IsPullback (spMap (algebraMap O (DualNumber O))) (𝟙 _) (𝟙 _)
      (spMap (algebraMap O (DualNumber O))) := IsPullback.of_vert_isIso ⟨by simp⟩
  have h := GlobalTheory.EpsThick.comb_bijective_of_isAffineOpen H hV
  refine Eq.mpr (congrArg Function.Bijective (funext fun ab => ?_)) h
  rw [Scheme.Hom.appLE_eq_app, _root_.mul_comm]
  rfl

end GlobalTheory.LieVB

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUniformization
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appell_humbert_uniformization : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → ∀ u : HolUnif X.A (X.diag c) (Module.finrank ℚ F),
    ∃ (u' : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (Hm : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ)
      (χ : u'.Λ → ℂ), u'.ex = u.ex ∧ u'.IsAH Hm χ := by
  first | exact @GlobalTheory.RealMult.Obj.exists_isAH_diag | exact GlobalTheory.RealMult.Obj.exists_isAH_diag | (intros; apply GlobalTheory.RealMult.Obj.exists_isAH_diag <;> assumption)

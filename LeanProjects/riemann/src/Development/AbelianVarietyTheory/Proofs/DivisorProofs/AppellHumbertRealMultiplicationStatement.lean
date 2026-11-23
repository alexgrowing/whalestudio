import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertRealMultiplication
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_real_multiplication : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) → (F →+* ℂ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ e j (a : F) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (Hm : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    ∀ (a : 𝓞 F) i j, e i (a : F) * Hm i j = Hm i j * starRingEnd ℂ (e j (a : F)) := by
  first | exact @GlobalTheory.RosatiAH.rosati_diag | exact GlobalTheory.RosatiAH.rosati_diag | (intros; apply GlobalTheory.RosatiAH.rosati_diag <;> assumption)

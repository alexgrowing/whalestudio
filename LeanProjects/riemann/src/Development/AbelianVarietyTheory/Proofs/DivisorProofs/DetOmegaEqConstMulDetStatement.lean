import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetOmegaEqConstMulDet
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_omega_eq_const_mul_det : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetOmega), ∃ C : ℂ,
    ∀ (v : Fin (Module.finrank ℚ F) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ j, u.IsDiff (W j) (v j).hom) → δ v = C * W.det := by
  first | exact @GlobalTheory.UnifDet.detOmega_eq_const_mul_det | exact GlobalTheory.UnifDet.detOmega_eq_const_mul_det | (intros; apply GlobalTheory.UnifDet.detOmega_eq_const_mul_det <;> assumption)

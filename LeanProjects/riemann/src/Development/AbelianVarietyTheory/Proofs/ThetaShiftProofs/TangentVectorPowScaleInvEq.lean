import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor CategoryTheory.MonObj

namespace GlobalTheory.AbelianLetters

theorem scale_tangent_pow (P : Out.PolAV (Sp ℂ)) (v : epsR ℂ ⟶ P.A) (n : ℕ) (hn : 0 < n) (hv : IsTangent v) :
    spMap (epsScaleR ((n : ℂ)⁻¹)) ≫ (v ^ n).left = v.left := by
  have h : GrpTangent.epsScale ((n : ℂ)⁻¹) ≫ (v ^ n) = v := by
    rw [GrpTangent.pow_eq_epsScale_comp hv, GrpTangent.epsScale_mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'),
      GrpTangent.epsScale_one, Category.id_comp]
  exact congrArg (fun φ => φ.left) h

end GlobalTheory.AbelianLetters

import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalFactorsOfParahoricVectorTwoBlockProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_factors_of_parahoricVector_twoBlockProduct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), IsParahoricVec χ (prod₂ σ₁ σ₂) f → f.1.1 1 ≠ 0 → IsSpherical σ₁ ∧ IsSpherical (twist σ₂ (detChar (Fin t) χ⁻¹)) := by
  first | exact @GlobalTheory.ParahoricSph.isSpherical_of_isParahoricVec | exact GlobalTheory.ParahoricSph.isSpherical_of_isParahoricVec | (intros; apply GlobalTheory.ParahoricSph.isSpherical_of_isParahoricVec <;> assumption)

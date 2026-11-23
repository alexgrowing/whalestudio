import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStandardSmoothLocalizationAwayJacobianDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardSmooth_localizationAway_jacobian_dvd : ∀ (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν), Function.Injective m → ∀ (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R), (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h → Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  first | exact @GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd | exact GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd | (intros; apply GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd <;> assumption)

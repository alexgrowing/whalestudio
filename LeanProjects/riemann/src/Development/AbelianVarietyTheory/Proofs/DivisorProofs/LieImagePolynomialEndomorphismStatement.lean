import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImagePolynomialEndomorphism
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_image_polynomial_endomorphism : ∀ (A : Over (Sp ℂ)) [GrpObj A] (Lb : LB A.left) (g : ℕ) (u : HolUnif A Lb g) (α : A ⟶ A) [IsMonHom α]
    (D : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)), (∀ z, u.ex (D z) = u.ex z ≫ α) →
    ∀ (h : HdR A) (v : epsR ℂ ⟶ A) (w : Fin g → ℂ) (c : ℂ), IsLieImage h v → u.IsDiff w v → D w = c • w →
    ∀ Q : Polynomial ℂ, ∃ v', IsLieImage (Polynomial.aeval (push (dp0 ℂ) (𝟙 _) α) Q h) v' ∧ u.IsDiff (Q.eval c • w) v' := by
  first | exact @GlobalTheory.LieImagePoly.exists_isLieImage_aeval | exact GlobalTheory.LieImagePoly.exists_isLieImage_aeval | (intros; apply GlobalTheory.LieImagePoly.exists_isLieImage_aeval <;> assumption)

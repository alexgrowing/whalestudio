import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLocalFactorization
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_local_factorization : ∀ (Λ : Type) [CommRing Λ] (ι₀ : Λ →+* ℂ) (M : Scheme.{0}) (s : M ⟶ Sp Λ) (V : M.Opens) (d : ℕ),
    SmoothOfRelativeDimension d (V.ι ≫ s) → ∀ (R : Type) [CommRing R] [Algebra ℂ R] [IsLocalRing R] (b : Sp R ⟶ M),
    (∀ x, b.base x ∈ V) → b ≫ s = spMap ((algebraMap ℂ R).comp ι₀) →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra ℂ B) (_ : Algebra.Smooth ℂ B) (g : Sp B ⟶ M) (j : B →ₐ[ℂ] R),
      spMap (j : B →+* R) ≫ g = b := by
  first | exact @GlobalTheory.AffChartSmooth.exists_smooth_chart | exact GlobalTheory.AffChartSmooth.exists_smooth_chart | (intros; apply GlobalTheory.AffChartSmooth.exists_smooth_chart <;> assumption)

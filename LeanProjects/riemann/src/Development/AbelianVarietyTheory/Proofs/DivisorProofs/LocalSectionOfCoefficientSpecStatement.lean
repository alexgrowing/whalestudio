import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSectionOfCoefficientSpec
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefSpecMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_of_coefficient_spec : ∀ (M : Scheme.{0}) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (b : Sp R ⟶ M)
    (W : M.Opens) (hW : IsAffineOpen W) (x : Sp R), b x ∈ W →
    ∃ (f : R) (_ : f ∉ x.asIdeal) (g : R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] Localization.Away f),
      spMap (g : R₀ ⊗[ℤ] Γ(M, W) →+* Localization.Away f) ≫ coefSpecMap hW R₀ =
        spMap (algebraMap R (Localization.Away f)) ≫ b := by
  first | exact @GlobalTheory.exists_away_factor_coefSpecMap | exact GlobalTheory.exists_away_factor_coefSpecMap | (intros; apply GlobalTheory.exists_away_factor_coefSpecMap <;> assumption)

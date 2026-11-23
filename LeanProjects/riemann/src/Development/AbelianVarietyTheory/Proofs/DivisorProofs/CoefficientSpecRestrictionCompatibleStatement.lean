import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpecRestrictionCompatible
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefSpecMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_spec_restriction_compatible : ∀ (M : Scheme.{0}) (W W' : M.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W)
    (R₀ : Type) [CommRing R₀],
    spMap (Algebra.TensorProduct.map (AlgHom.id R₀ R₀) (M.presheaf.map (homOfLE hle).op).hom.toIntAlgHom :
      R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W')).toRingHom ≫ coefSpecMap hW R₀ = coefSpecMap hW' R₀ := by
  first | exact @GlobalTheory.RealMult.spMap_restrict_comp_coefSpecMap | exact GlobalTheory.RealMult.spMap_restrict_comp_coefSpecMap | (intros; apply GlobalTheory.RealMult.spMap_restrict_comp_coefSpecMap <;> assumption)

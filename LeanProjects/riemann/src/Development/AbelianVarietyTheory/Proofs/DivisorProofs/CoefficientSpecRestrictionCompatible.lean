import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefSpecMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem spMap_restrict_comp_coefSpecMap : ∀ (M : Scheme.{0}) (W W' : M.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W)
    (R₀ : Type) [CommRing R₀],
    spMap (Algebra.TensorProduct.map (AlgHom.id R₀ R₀) (M.presheaf.map (homOfLE hle).op).hom.toIntAlgHom :
      R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W')).toRingHom ≫ coefSpecMap hW R₀ = coefSpecMap hW' R₀ := by
  intro M W W' hW hW' hle R₀ _
  unfold coefSpecMap spMap
  rw [← hW.map_fromSpec hW' (homOfLE hle).op, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2

end GlobalTheory.RealMult

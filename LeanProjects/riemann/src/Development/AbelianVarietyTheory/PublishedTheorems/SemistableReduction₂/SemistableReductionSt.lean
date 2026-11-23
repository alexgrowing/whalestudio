import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Published

def SemistableReductionSt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (P : Out.PolAV (Sp K)),
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (G : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G), IsSemiAbelian G ∧
        ∃ φ : pullback G.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶ P.A.left,
          IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G) P.A
            (spMap (IntermediateField.inclusion h).toRingHom) φ

namespace SemistableReductionSt

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]

theorem of_semiAbelian_model (G : Over (Sp (integralClosure ℤ_[p] K))) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (G' : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G'), IsSemiAbelian G' ∧
        ∃ φ : pullback G'.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶
            ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G).left,
          IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G')
            ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G)
            (spMap (IntermediateField.inclusion h).toRingHom) φ := by
  refine ⟨K, le_rfl, inferInstance, G, inferInstance, hG, 𝟙 _, ?_⟩
  have h : spMap (IntermediateField.inclusion (le_refl K)).toRingHom = 𝟙 (Sp K) := by
    rw [← Spec.map_id]
    congr 1
  have : IsMonHom (Iso.refl ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G)).hom :=
    inferInstanceAs (IsMonHom (𝟙 _))
  exact (isGrpPullback_of_iso (Iso.refl _)).congr h.symm rfl

theorem of_goodReduction (G : Over (Sp (integralClosure ℤ_[p] K))) [GrpObj G] (hG : IsAbelianScheme G) :
    IsAbelianScheme ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G) ∧
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K'), FiniteDimensional ℚ_[p] K' ∧
      ∃ (G' : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G'), IsSemiAbelian G' ∧
        ∃ φ : pullback G'.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶
            ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G).left,
          IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G')
            ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K) K))).obj G)
            (spMap (IntermediateField.inclusion h).toRingHom) φ :=
  ⟨isAbelianScheme_pullback_obj _ G hG, of_semiAbelian_model p K G (isSemiAbelian_of_isAbelianScheme G hG)⟩

end SemistableReductionSt

end GlobalTheory.Published
end

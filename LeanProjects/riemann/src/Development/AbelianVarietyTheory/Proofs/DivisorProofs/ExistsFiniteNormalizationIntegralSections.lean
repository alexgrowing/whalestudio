import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelObjIsoHomSubtype
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
open Scheme.AffineZariskiSite

noncomputable section

theorem exists_finite_of_isFinSub : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsIntegral S] [IsDominant gp]
    (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)), IsFinSub gp F →
    ∃ (S' : Scheme.{0}) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  first
  | exact @_root_.GlobalTheory.RelativeSpectrum.exists_finite_cover
  | exact _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover
  | (apply _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover ..)

end

end GlobalTheory.Mum

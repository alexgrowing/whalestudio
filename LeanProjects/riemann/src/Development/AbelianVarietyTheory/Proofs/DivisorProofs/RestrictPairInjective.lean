import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPairRestrictBaseChangeBijective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs.PairInj

theorem pull2_pairRes_restrict (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {X₀ Z₀ : Scheme.{0}}
    (t₀ : Z₀ ⟶ Sp R₀) (f₀ : Z₀ ⟶ X₀) {D : Type} [Category.{0} D] (K : D ⥤ (Pair f₀)ᵒᵖ)
    (c : CatCoh.H2 (ext R₁ (OAff t₀))) :
    (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairRes f₀ t₀)).pull2 c) =
      (extMap R₁ (CoefMap.restrict (OAff t₀) (K ⋙ pairFst f₀))).pull2 c := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
  refine congrArg _ (Subtype.ext ?_)
  funext T T' T'' a b
  show extHom R₁ (coefHom (CoefMap.restrict (OPair f₀ t₀) K) T'')
      (extHom R₁ (coefHom (pairRes f₀ t₀) (K.obj T'')) _) =
    extHom R₁ (coefHom (CoefMap.restrict (OAff t₀) (K ⋙ pairFst f₀)) T'') _
  exact (PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).trans ((PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).trans
    (PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).symm)

theorem restrict_pair_injective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ Z₀ : Scheme.{0}) (t₀ : Z₀ ⟶ Sp R₀) (f₀ : Z₀ ⟶ X₀) (D : Type) [Category.{0} D] [Quiver.IsThin D] (K : D ⥤ (Pair f₀)ᵒᵖ), IsBas (opOf (K ⋙ pairFst f₀)) → Function.Injective (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 := by
  intro R₀ R₁ _ _ _ X₀ Z₀ t₀ f₀ D _ _ K hB x y e
  have hG := (BasisExt.restrict_ext_bijective R₀ R₁ Z₀ t₀ D (K ⋙ pairFst f₀) hB.1 hB.2).2.1
  have hP := ((PairExt.pairRes_ext_bijective R₀ R₁ X₀ Z₀ t₀ f₀).1.2).2
  obtain ⟨x0, rfl⟩ := hP x
  obtain ⟨y0, rfl⟩ := hP y
  rw [pull2_pairRes_restrict, pull2_pairRes_restrict] at e
  rw [hG e]

end GlobalTheory.LBObs.PairInj

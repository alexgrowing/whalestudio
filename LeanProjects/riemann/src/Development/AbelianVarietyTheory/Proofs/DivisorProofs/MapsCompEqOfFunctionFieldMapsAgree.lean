import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem Dbl.p_comp_eq_of_isHom : ∀ (F : Type) [Field F] (X Y : Var F) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), (ratOf X).IsHom (ratOf Y) φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → W.p₁ ≫ f = W.p₂ ≫ f := by
  intro F _ X Y φ f hf W hW
  haveI : IsDominant (W.Z.fromSpecStalk (genericPoint W.Z)) := ⟨by
    rw [DenseRange, dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec W.Z).def]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩)⟩
  haveI : IsSeparated X.str := (ratOf X).sep
  have hs : f ≫ X.str = Y.str := hf.inducedModelMorphism_comp_structureMap
  refine ext_of_isDominant_of_isSeparated X.str ?_ (W.Z.fromSpecStalk (genericPoint W.Z)) ?_
  · change (W.p₁ ≫ f) ≫ X.str = (W.p₂ ≫ f) ≫ X.str
    rw [Category.assoc, Category.assoc, hs, W.str_eq]
  · have e₁ := specMap_functionFieldMap W.p₁
    have e₂ := specMap_functionFieldMap W.p₂
    have hφ : (functionFieldMap W.p₁).comp φ.toRingHom = (functionFieldMap W.p₂).comp φ.toRingHom :=
      RingHom.ext hW
    have key : ∀ (α : Y.Fn →+* W.Z.functionField),
        Spec.map (CommRingCat.ofHom α) ≫ genericFieldPoint Y.X ≫ f =
          Spec.map (CommRingCat.ofHom (α.comp φ.toRingHom)) ≫ (ratOf X).pt := by
      intro α
      have hf' : genericFieldPoint Y.X ≫ f = spMap φ.toRingHom ≫ (ratOf X).pt := hf
      rw [hf', CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      rfl
    change genericFieldPoint W.Z ≫ W.p₁ ≫ f = genericFieldPoint W.Z ≫ W.p₂ ≫ f
    rw [← Category.assoc, ← e₁, Category.assoc, ← Category.assoc (genericFieldPoint W.Z), ← e₂, Category.assoc,
      key, key, hφ]

end GlobalTheory.FlagPush

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CurveRootGeometry

theorem exists_genPt_comp_of_generic {C C' : Scheme.{0}} [IsIntegral C] [IsIntegral C'] (π : C' ⟶ C)
    (h : π (genericPoint C') = genericPoint C) :
    ∃ f : Sp C'.functionField ⟶ Sp C.functionField, f ≫ genPt C = genPt C' ≫ π := by
  have key : ∀ y : C, π (genericPoint C') = y →
      ∃ f : Spec (C'.presheaf.stalk (genericPoint C')) ⟶ Spec (C.presheaf.stalk y),
        f ≫ C.fromSpecStalk y = C'.fromSpecStalk (genericPoint C') ≫ π := by
    rintro y rfl
    exact ⟨Spec.map (π.stalkMap _), Scheme.SpecMap_stalkMap_fromSpecStalk π⟩
  exact key _ h

theorem abGen_of_isActPull : ∀ (O : Type) [CommRing O] (c : O →+* O) (C C' : Scheme.{0}) [IsIntegral C] [IsIntegral C']
    (π : C' ⟶ C), π (genericPoint C') = genericPoint C → ∀ (G : Over C) [GrpObj G] (i : OAct O G) (G' : Over C')
    [GrpObj G'] (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i π φ → AbGen c i → AbGen c i' := by
  intro O _ c C C' _ _ π hπ G _ i G' _ i' φ hφ ⟨P, j, χ, hχ, hr⟩
  obtain ⟨f, hf⟩ := exists_genPt_comp_of_generic π hπ
  obtain ⟨P', j', ψ, hψ, hr'⟩ := GlobalTheory.TorusPart.exists_isActPull_isRosati O c _ _ f P j hr
  have hc := hψ.comp hχ
  rw [hf] at hc
  have w : (ψ ≫ χ) ≫ G.hom = (P'.A.hom ≫ genPt C') ≫ π := by
    rw [Category.assoc P'.A.hom]; exact hc.1.1.w
  have e₁ := hφ.1.1.lift_fst _ _ w
  have e₂ := hφ.1.1.lift_snd _ _ w
  refine ⟨P', j', hφ.1.1.lift _ _ w, ⟨IsGrpPullback.cancel hφ.1 (by rw [e₁]; exact hc.1) e₂, fun a => ?_⟩, hr'⟩
  apply hφ.1.1.hom_ext
  · rw [Category.assoc, e₁, hc.2, Category.assoc _ (i'.act a).left, hφ.2, ← Category.assoc _ φ, e₁]
  · rw [Category.assoc, e₂, Category.assoc _ (i'.act a).left, Over.w, e₂, ← Category.assoc, Over.w]

end GlobalTheory.CurveRootGeometry

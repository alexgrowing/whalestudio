import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartAt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

theorem aH_left_π_ptMap {G' : Over (Sp O)} {π : G'.left ⟶ t.G.left}
    (hπ : IsPullback π G'.hom t.G.hom (spMap x0 ≫ ξ)) {D : Type} [CommRing D] [Algebra O D]
    (a : Bt P' x0 hu →ₐ[O] D) :
    (ptMap a ≫ aH P' x0 hu hπ).left ≫ π = spMap (a.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left := by
  rw [Over.comp_left, Category.assoc, aH_left_π]
  change spMap a.toRingHom ≫ spMap (inB P' x0 hu) ≫ P'.u.left = _
  rw [GlobalTheory.HTMap.spc_assoc]

theorem str_of_alg {D : Type} [CommRing D] [Algebra O D] (a : Bt P' x0 hu →ₐ[O] D) :
    (a.toRingHom.comp (inB P' x0 hu)).comp P'.str = (algebraMap O D).comp x0 := by
  rw [RingHom.comp_assoc, inB_str, ← RingHom.comp_assoc]
  congr 1
  exact a.comp_algebraMap

theorem at_alg {D : Type} [CommRing D] [Algebra O D] (a : Bt P' x0 hu →ₐ[O] D) :
    P'.At ((algebraMap O D).comp x0) (spMap (a.toRingHom.comp (inB P' x0 hu)) ≫ P'.u.left)
      (a.toRingHom.comp (inB P' x0 hu)) :=
  ⟨str_of_alg P' x0 hu a, rfl⟩

theorem exists_mul_affine {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ t.G.left}
    (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) {D : Type} [CommRing D] [Algebra O D]
    (a b : Bt P' x0 hu →ₐ[O] D) :
    ∃ z : specO O D ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 =
      (ptMap a ≫ aH P' x0 hu hg.1) * (ptMap b ≫ aH P' x0 hu hg.1) := by
  have ha := at_alg P' x0 hu a
  have hb := at_alg P' x0 hu b
  let w₁ : Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (ha.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  let w₂ : Over.mk ((specO O D).hom ≫ spMap x0 ≫ ξ) ⟶ t.G :=
    GlobalTheory.HTMap.mkPt _ (hb.over.trans (GlobalTheory.HTMap.spc_assoc _ _ _).symm)
  obtain ⟨β'', h''⟩ := GlobalTheory.HTMap.FP.At.mul (w := w₁) (w' := w₂) ha hb
  refine ⟨ptOf P' x0 hu β'' h''.1, ?_⟩
  refine Over.OverMorphism.ext (hg.1.hom_ext ?_ ?_)
  · rw [ptOf_aH_π, h''.2]
    exact hg.2 (specO O D) _ _ w₁ w₂ (aH_left_π_ptMap P' x0 hu hg.1 a).symm
      (aH_left_π_ptMap P' x0 hu hg.1 b).symm
  · rw [Over.w, Over.w]

end GlobalTheory.FinPartAt

namespace GlobalTheory.FinPartAt

theorem exists_mul_factor {O : Type} [CommRing O] {C : Type} [CommRing C] [Algebra O C] (S : Over (Sp O))
    (x y : S ⟶ specO O C) :
    ∃ c : S ⟶ specO O (C ⊗[O] C),
      c ≫ ptMap (Algebra.TensorProduct.includeLeft : C →ₐ[O] C ⊗[O] C) = x ∧
      c ≫ ptMap (Algebra.TensorProduct.includeRight : C →ₐ[O] C ⊗[O] C) = y := by
  have hxy : x.left ≫ (specO O C).hom = y.left ≫ (specO O C).hom := by rw [Over.w, Over.w]
  let l := pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom
  have hl : l ≫ (specO O (C ⊗[O] C)).hom = S.hom := by
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O (C ⊗[O] C))) = _
    rw [Category.assoc, pullbackSpecIso_hom_base, ← Category.assoc]
    erw [pullback.lift_fst]
    exact Over.w x
  refine ⟨Over.homMk l hl, ?_, ?_⟩
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom)) = _
    rw [Category.assoc, pullbackSpecIso_hom_fst]
    erw [pullback.lift_fst]
  · refine Over.OverMorphism.ext ?_
    change (pullback.lift x.left y.left hxy ≫ (pullbackSpecIso O C C).hom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) = _
    rw [Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    erw [pullback.lift_snd]

theorem exists_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (q : ℕ) (P' : GlobalTheory.HTMap.FP t ξ q) (O : Type) [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f)) (G' : Over (Sp O)) [GrpObj G'] (π : G'.left ⟶ t.G.left) (hg : IsGrpPullback G' t.G (spMap x0 ≫ ξ) π) (S : Over (Sp O)) (x y : S ⟶ Hs P' x0 hu), ∃ z : S ⟶ Hs P' x0 hu, z ≫ aH P' x0 hu hg.1 = (x ≫ aH P' x0 hu hg.1) * (y ≫ aH P' x0 hu hg.1) := by
  intro E _ _ _ H X t R _ ξ q P' O _ x0 hu G' _ π hg S x y
  obtain ⟨c, hc₁, hc₂⟩ := exists_mul_factor S x y
  obtain ⟨z₀, hz₀⟩ := exists_mul_affine P' x0 hu hg
    (Algebra.TensorProduct.includeLeft : Bt P' x0 hu →ₐ[O] Bt P' x0 hu ⊗[O] Bt P' x0 hu)
    Algebra.TensorProduct.includeRight
  refine ⟨c ≫ z₀, ?_⟩
  rw [Category.assoc, hz₀, MonObj.comp_mul, ← Category.assoc, hc₁, ← Category.assoc, hc₂]

end GlobalTheory.FinPartAt

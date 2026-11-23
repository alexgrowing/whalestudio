import Mathlib
import GroundTheory.TateCohomology.TateShapiro
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]

omit [Fintype G] [Fintype S] in

lemma shortExact_map_resFunctor {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) :
    (X.map (resFunctor S.subtype)).ShortExact :=
  (Rep.shortExact_res S.subtype).2 hX

section Res

noncomputable def tateRes (n : ℤ) :
    tateCohomologyFunctor (R := k) (G := G) n ⟶
      resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (Rep.resCoindAdjunction.{u, u} k S.subtype).unit _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (resFunctor S.subtype) (tateCoindNatIso S n).hom

lemma tateRes_app (n : ℤ) (A : Rep.{u} k G) :
    (tateRes S n).app A =
      (tateCohomologyFunctor n).map ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app A) ≫
        (tateCoindIso S (res S.subtype A) n).hom := by
  simp only [tateRes, NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

theorem tateRes_naturality {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℤ) :
    (tateCohomologyFunctor n).map f ≫ (tateRes S n).app B =
      (tateRes S n).app A ≫ (resFunctor S.subtype ⋙ tateCohomologyFunctor n).map f :=
  (tateRes S n).naturality f

@[simps]
noncomputable def resCoindUnitShortComplex (X : ShortComplex (Rep.{u} k G)) :
    X ⟶ (X.map (resFunctor S.subtype)).map (coindFunctor k S.subtype) where
  τ₁ := (Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app X.X₁
  τ₂ := (Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app X.X₂
  τ₃ := (Rep.resCoindAdjunction.{u, u} k S.subtype).unit.app X.X₃
  comm₁₂ := ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.naturality X.f).symm
  comm₂₃ := ((Rep.resCoindAdjunction.{u, u} k S.subtype).unit.naturality X.g).symm

theorem tateRes_δ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ hX n ≫ (tateRes S (n + 1)).app X.X₁ =
      (tateRes S n).app X.X₃ ≫ TateCohomology.δ (shortExact_map_resFunctor S hX) n := by
  have hR := shortExact_map_resFunctor S hX
  have h1 := TateCohomology.δ_naturality hX (shortExact_map_coindFunctor S hR)
    (resCoindUnitShortComplex S X) n
  have h2 := tateCoindIso_δ S hR n
  simp only [resCoindUnitShortComplex_τ₁, resCoindUnitShortComplex_τ₃] at h1
  rw [tateRes_app, tateRes_app]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h1).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

end Res

section Cores

open scoped Classical in

noncomputable def tateCores (n : ℤ) :
    resFunctor S.subtype ⋙ tateCohomologyFunctor (R := k) (G := S) n ⟶
      tateCohomologyFunctor (R := k) (G := G) n :=
  Functor.whiskerLeft (resFunctor S.subtype) (tateIndNatIso S n).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Rep.indResAdjunction.{u} k S.subtype).counit _ ≫
    (Functor.leftUnitor _).hom

lemma tateCores_app (n : ℤ) (A : Rep.{u} k G) :
    (tateCores S n).app A =
      (tateIndIso S (res S.subtype A) n).inv ≫
        (tateCohomologyFunctor n).map ((Rep.indResAdjunction.{u} k S.subtype).counit.app A) := by
  simp only [tateCores, NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.whiskerLeft_app, Category.id_comp]
  rfl

theorem tateCores_naturality {A B : Rep.{u} k G} (f : A ⟶ B) (n : ℤ) :
    (resFunctor S.subtype ⋙ tateCohomologyFunctor n).map f ≫ (tateCores S n).app B =
      (tateCores S n).app A ≫ (tateCohomologyFunctor n).map f :=
  (tateCores S n).naturality f

@[simps]
noncomputable def indResCounitShortComplex (X : ShortComplex (Rep.{u} k G)) :
    (X.map (resFunctor S.subtype)).map (indFunctor k S.subtype) ⟶ X where
  τ₁ := (Rep.indResAdjunction.{u} k S.subtype).counit.app X.X₁
  τ₂ := (Rep.indResAdjunction.{u} k S.subtype).counit.app X.X₂
  τ₃ := (Rep.indResAdjunction.{u} k S.subtype).counit.app X.X₃
  comm₁₂ := ((Rep.indResAdjunction.{u} k S.subtype).counit.naturality X.f).symm
  comm₂₃ := ((Rep.indResAdjunction.{u} k S.subtype).counit.naturality X.g).symm

theorem tateCores_δ {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact) (n : ℤ) :
    TateCohomology.δ (shortExact_map_resFunctor S hX) n ≫ (tateCores S (n + 1)).app X.X₁ =
      (tateCores S n).app X.X₃ ≫ TateCohomology.δ hX n := by
  have hR := shortExact_map_resFunctor S hX
  have h1 := TateCohomology.δ_naturality (shortExact_map_indFunctor S hR) hX
    (indResCounitShortComplex S X) n
  have h2 := tateIndIso_δ S hR n
  simp only [indResCounitShortComplex_τ₁, indResCounitShortComplex_τ₃] at h1
  have h3 : TateCohomology.δ hR n ≫ (tateIndIso S (X.map (resFunctor S.subtype)).X₁ (n + 1)).inv =
      (tateIndIso S (X.map (resFunctor S.subtype)).X₃ n).inv ≫
        TateCohomology.δ (shortExact_map_indFunctor S hR) n := by
    exact (Iso.inv_hom_id_assoc _ _).symm.trans (congrArg (_ ≫ ·)
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))))))
  rw [tateCores_app, tateCores_app]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h3).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h1).trans (Category.assoc _ _ _).symm)))

end Cores

end GroundTheory.GroupCoh

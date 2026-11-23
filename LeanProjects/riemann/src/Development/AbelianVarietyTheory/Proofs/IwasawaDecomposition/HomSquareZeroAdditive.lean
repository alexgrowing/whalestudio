import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroAdd

variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing C]
    [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    Formalism.L2.Pj.homAt x0 (g.comp f) = Formalism.L2.Pj.homAt x0 g ≫ Formalism.L2.Pj.homAt x0 f := by
  apply Over.OverMorphism.ext
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem homAt_id {A : Type} [CommRing A] [Algebra S A] :
    Formalism.L2.Pj.homAt x0 (AlgHom.id S A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show Spec.map _ = 𝟙 _
  exact Spec.map_id _

theorem comp_one' {Y Z M : Over X} [GrpObj M] (f : Y ⟶ Z) : f ≫ (1 : Z ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (f ≫ toUnit Z) (toUnit Y)]

variable {G : Over X} [GrpObj G]
variable {V W : Type} [AddCommGroup V] [Module S V] [Module Sᵐᵒᵖ V] [IsCentralScalar S V]
    [AddCommGroup W] [Module S W] [Module Sᵐᵒᵖ W] [IsCentralScalar S W]

theorem map_comp_map {U : Type} [AddCommGroup U] [Module S U] [Module Sᵐᵒᵖ U] [IsCentralScalar S U]
    (f : W →ₗ[S] V) (g : V →ₗ[S] U) :
    Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (g ∘ₗ f)) =
      Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map g) ≫ Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map f) := by
  rw [← homAt_comp]
  congr 1
  refine AlgHom.ext fun x => ?_
  ext <;> simp

theorem map_id_homAt : Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (LinearMap.id : W →ₗ[S] W)) = 𝟙 _ := by
  rw [← homAt_id]
  congr 1
  refine AlgHom.ext fun x => ?_
  ext <;> simp

theorem map_zero_comp (y : overAt x0 (TrivSqZeroExt S W) ⟶ G)
    (hy : Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.fstHom S S W) ≫ y = 1) :
    Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (0 : W →ₗ[S] V)) ≫ y = 1 := by
  have e : (TrivSqZeroExt.map (0 : W →ₗ[S] V)) =
      (TrivSqZeroExt.inlAlgHom S S V).comp (TrivSqZeroExt.fstHom S S W) := by
    refine AlgHom.ext fun x => ?_
    ext <;> simp
  rw [e, homAt_comp, Category.assoc, hy, comp_one']

end GlobalTheory.SqZeroAdd

namespace GlobalTheory.SqZeroAdd

variable {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
variable {G : Over X} [GrpObj G]
variable {W : Type} [AddCommGroup W] [Module S W] [Module Sᵐᵒᵖ W] [IsCentralScalar S W]

theorem key (y : overAt x0 (TrivSqZeroExt S W) ⟶ G)
    (hy : Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.fstHom S S W) ≫ y = 1) :
    Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (LinearMap.inl S W W + LinearMap.inr S W W)) ≫ y =
      (Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (LinearMap.inl S W W)) ≫ y) *
        (Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (LinearMap.inr S W W)) ≫ y) := by
  ext1
  refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
    (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst S W W)).toRingHom)
    (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd S W W)).toRingHom) ?_ ?_ ?_ ?_
  · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst S W W)).toRingHom
      (fun x => ⟨1, one_pos, TrivSqZeroExt.map (LinearMap.inl S W W) x, by ext <;> simp⟩)
      fun d hd => ?_).surjective
    have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
    exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
  · intro d h₁ h₂
    have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
    have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
    have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
    exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
  · refine congrArg Over.Hom.left
      (?_ : Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (LinearMap.fst S W W)) ≫ _ =
        Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (LinearMap.fst S W W)) ≫ _)
    rw [comp_mul]
    simp only [← Category.assoc, ← map_comp_map]
    have e₁ : LinearMap.fst S W W ∘ₗ (LinearMap.inl S W W + LinearMap.inr S W W) = LinearMap.id := by
      ext; simp
    have e₂ : LinearMap.fst S W W ∘ₗ LinearMap.inl S W W = LinearMap.id := by ext; simp
    have e₃ : LinearMap.fst S W W ∘ₗ LinearMap.inr S W W = 0 := by ext; simp
    rw [e₁, e₂, e₃, map_id_homAt, map_zero_comp x0 y hy, Category.id_comp, _root_.mul_one]
  · refine congrArg Over.Hom.left
      (?_ : Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (LinearMap.snd S W W)) ≫ _ =
        Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (LinearMap.snd S W W)) ≫ _)
    rw [comp_mul]
    simp only [← Category.assoc, ← map_comp_map]
    have e₁ : LinearMap.snd S W W ∘ₗ (LinearMap.inl S W W + LinearMap.inr S W W) = LinearMap.id := by
      ext; simp
    have e₂ : LinearMap.snd S W W ∘ₗ LinearMap.inl S W W = 0 := by ext; simp
    have e₃ : LinearMap.snd S W W ∘ₗ LinearMap.inr S W W = LinearMap.id := by ext; simp
    rw [e₁, e₂, e₃, map_id_homAt, map_zero_comp x0 y hy, Category.id_comp, _root_.one_mul]

theorem map_add_comp :
    ∀ {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
    {V W : Type} [AddCommGroup V] [Module S V] [Module Sᵐᵒᵖ V] [IsCentralScalar S V]
    [AddCommGroup W] [Module S W] [Module Sᵐᵒᵖ W] [IsCentralScalar S W]
    (y : overAt x0 (TrivSqZeroExt S W) ⟶ G), Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.fstHom S S W) ≫ y = 1 →
    ∀ f g : W →ₗ[S] V, Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (f + g)) ≫ y =
      (Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map f) ≫ y) * (Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map g) ≫ y) := by
  intro X G _ S _ x0 V W _ _ _ _ _ _ _ _ y hy f g
  have h := congrArg (Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (f.coprod g)) ≫ ·) (key x0 y hy)
  simp only [comp_mul, ← Category.assoc, ← map_comp_map] at h
  have e₁ : f.coprod g ∘ₗ (LinearMap.inl S W W + LinearMap.inr S W W) = f + g := by ext; simp
  have e₂ : f.coprod g ∘ₗ LinearMap.inl S W W = f := by ext; simp
  have e₃ : f.coprod g ∘ₗ LinearMap.inr S W W = g := by ext; simp
  rwa [e₁, e₂, e₃] at h

end GlobalTheory.SqZeroAdd

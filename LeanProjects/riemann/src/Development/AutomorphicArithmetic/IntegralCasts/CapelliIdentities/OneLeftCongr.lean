import Mathlib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
private noncomputable def UpperTheory.specMapOverOfAlgHom {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A B : Type} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ x) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ x) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact f.comp_algebraMap)

open AlgebraicGeometry CategoryTheory in
private theorem UpperTheory.specMapAlg_comp {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    UpperTheory.specMapOverOfAlgHom x g ≫ UpperTheory.specMapOverOfAlgHom x f = UpperTheory.specMapOverOfAlgHom x (g.comp f) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

open AlgebraicGeometry CategoryTheory in
private theorem UpperTheory.specMap_id {S : Scheme.{0}} {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) {A : Type} [CommRing A] [Algebra R A] :
    UpperTheory.specMapOverOfAlgHom x (AlgHom.id R A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
private theorem UpperTheory.grpObj_one_left_congr {S : Scheme.{0}} (G : Over S) [GrpObj G]
    {X : Scheme.{0}} {x y : X ⟶ S} (h : x = y) :
    (1 : Over.mk x ⟶ G).left = (1 : Over.mk y ⟶ G).left := by
  subst h
  rfl

theorem UpperTheory.tangent_left_one :
    open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
        ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S)
          (v w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x) ⟶ G),
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ v.left = (1 : Over.mk x ⟶ G).left →
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ w.left = (1 : Over.mk x ⟶ G).left →
            ∃ u : Spec (CommRingCat.of (TrivSqZeroExt R (R × R))) ⟶ G.left,
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R (R × R)).toRingHom) ≫ u = (1 : Over.mk x ⟶ G).left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom) ≫ u = v.left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ≫ u = w.left ∧
              Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)).toRingHom) ≫ u
                = (v * w).left := by
  open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
  · intro S G _ R _ x v w hv hw
    have hx : Spec.map (CommRingCat.ofHom (algebraMap R R)) ≫ x = x := by
      have : Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ := Spec.map_id _
      rw [this, Category.id_comp]
    have h1 := UpperTheory.grpObj_one_left_congr G hx
    have hv' : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R R) ≫ v = 1 :=
      Over.OverMorphism.ext (hv.trans h1.symm)
    have hw' : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R R) ≫ w = 1 :=
      Over.OverMorphism.ext (hw.trans h1.symm)
    have e0 : (TrivSqZeroExt.map (0 : R →ₗ[R] R)) =
        (Algebra.ofId R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R) := by
      apply AlgHom.ext
      intro a
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    have hv0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (0 : R →ₗ[R] R)) ≫ v = 1 := by
      rw [e0, ← UpperTheory.specMapAlg_comp, Category.assoc, hv', MonObj.comp_one]
    have hw0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (0 : R →ₗ[R] R)) ≫ w = 1 := by
      rw [e0, ← UpperTheory.specMapAlg_comp, Category.assoc, hw', MonObj.comp_one]
    let U : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (TrivSqZeroExt R (R × R)))) ≫ x) ⟶ G :=
      (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.inl R R R)) ≫ v) *
        (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.inr R R R)) ≫ w)
    have key : ∀ f : (R × R) →ₗ[R] R, UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map f) ≫ U =
        (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (f ∘ₗ LinearMap.inl R R R)) ≫ v) *
          (UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (f ∘ₗ LinearMap.inr R R R)) ≫ w) := by
      intro f
      simp only [U, MonObj.comp_mul, ← Category.assoc, UpperTheory.specMapAlg_comp,
        TrivSqZeroExt.map_comp_map]
    have k0 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.fstHom R R (R × R)) ≫ U = 1 := by
      simp only [U, MonObj.comp_mul, ← Category.assoc, UpperTheory.specMapAlg_comp,
        TrivSqZeroExt.fstHom_comp_map]
      rw [hv', hw', _root_.mul_one]
    have k1 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.fst R R R)) ≫ U = v := by
      rw [key, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hw0, TrivSqZeroExt.map_id,
        UpperTheory.specMap_id, Category.id_comp, _root_.mul_one]
    have k2 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.snd R R R)) ≫ U = w := by
      rw [key, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hv0, TrivSqZeroExt.map_id,
        UpperTheory.specMap_id, Category.id_comp, _root_.one_mul]
    have k3 : UpperTheory.specMapOverOfAlgHom x (TrivSqZeroExt.map (LinearMap.fst R R R + LinearMap.snd R R R)) ≫ U
        = v * w := by
      rw [key, LinearMap.add_comp, LinearMap.add_comp, LinearMap.fst_comp_inl,
        LinearMap.fst_comp_inr, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, add_zero, zero_add,
        TrivSqZeroExt.map_id, UpperTheory.specMap_id, Category.id_comp, Category.id_comp]
    exact ⟨U.left, (congrArg CommaMorphism.left k0).trans h1, congrArg CommaMorphism.left k1,
      congrArg CommaMorphism.left k2, congrArg CommaMorphism.left k3⟩

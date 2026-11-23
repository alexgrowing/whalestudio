import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

noncomputable section

namespace GlobalTheory

abbrev specOver (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))

theorem hom_ext_of_fromSpecStalk {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : ∀ x, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by
  have key : ∀ x : X, ∃ e : f x = g x, f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ g.stalkMap x := by
    intro x
    have e1 : (SpecToEquivOfLocalRing Y (X.presheaf.stalk x)).symm ⟨f x, f.stalkMap x, inferInstance⟩ =
        (SpecToEquivOfLocalRing Y (X.presheaf.stalk x)).symm ⟨g x, g.stalkMap x, inferInstance⟩ := by
      simp only [SpecToEquivOfLocalRing_symm_apply]
      rw [Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk, h x]
    exact SpecToEquivOfLocalRing_eq_iff.mp ((Equiv.injective _) e1)
  have hc : ∀ (U : Y.Opens) (s : Γ(Y, U)) (y y' : Y) (e : y = y') (hy : y ∈ U) (hy' : y' ∈ U),
      (Y.presheaf.stalkCongr (Inseparable.of_eq e)).hom (Y.presheaf.germ U y hy s) =
        Y.presheaf.germ U y' hy' s := by
    rintro U s y _ rfl hy hy'
    simp
  refine Scheme.Hom.ext ?_ fun U => ?_
  · ext x
    exact (key x).1
  · ext s
    apply TopCat.Presheaf.section_ext X.sheaf
    intro x hx
    obtain ⟨e, he⟩ := key x
    have hfx : f x ∈ U := e ▸ hx
    change X.presheaf.germ _ x hx _ = X.presheaf.germ _ x hx _
    rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply,
      ← Scheme.Hom.germ_stalkMap_apply f U x hfx, ← Scheme.Hom.germ_stalkMap_apply g U x hx, he,
      CommRingCat.comp_apply, hc U s (f x) (g x) e hfx hx]

theorem hom_ext_of_isLocalRing {A : Type u} [CommRing A] {Y : Scheme.{u}}
    {f g : Spec (.of A) ⟶ Y}
    (h : ∀ (B : Type u) [CommRing B] [IsLocalRing B] (φ : A →+* B),
      Spec.map (CommRingCat.ofHom φ) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ g) : f = g := by
  apply hom_ext_of_fromSpecStalk
  intro x
  rw [Spec.fromSpecStalk_eq']
  exact h ((Spec (.of A)).presheaf.stalk x) (StructureSheaf.toStalk _ _).hom

section Glue

variable {R : Type u} [CommRing R]

theorem exists_over_hom_of_locally {T Y : Over (Spec (.of R))} [IsReduced T.left]
    [IsSeparated Y.hom]
    (F : ∀ (k : Type u) [Field k] [Algebra R k], (specOver R k ⟶ T) → (specOver R k ⟶ Y))
    (H : ∀ t : T.left, ∃ (U : Over (Spec (.of R))) (j : U ⟶ T) (_ : IsOpenImmersion j.left)
      (f : U ⟶ Y), t ∈ Set.range j.left ∧
        ∀ (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ U), x ≫ f = F k (x ≫ j)) :
    ∃ f : T ⟶ Y, ∀ (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ T),
      x ≫ f = F k x := by
  choose U j hj fU hmem hfU using H
  let 𝒰 : T.left.OpenCover :=
    { I₀ := T.left, X i := (U i).left, f i := (j i).left,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun t ↦ ⟨t, by simpa using hmem t⟩, fun i ↦ hj i⟩ }
  have hcomp : ∀ a b, pullback.fst (j a).left (j b).left ≫ (fU a).left =
      pullback.snd (j a).left (j b).left ≫ (fU b).left := by
    intro a b
    have := hj a
    have := hj b
    let P : Over (Spec (.of R)) :=
      Over.mk (pullback.fst (j a).left (j b).left ≫ (j a).left ≫ T.hom)
    haveI : IsReduced P.left :=
      isReduced_of_isOpenImmersion (pullback.fst (j a).left (j b).left ≫ (j a).left)
    let p₁ : P ⟶ U a := Over.homMk (pullback.fst _ _) (by
      show _ = pullback.fst _ _ ≫ (j a).left ≫ T.hom
      rw [Over.w])
    let p₂ : P ⟶ U b := Over.homMk (pullback.snd _ _) (by
      show _ = pullback.fst _ _ ≫ (j a).left ≫ T.hom
      rw [pullback.condition_assoc, Over.w])
    have hp : p₁ ≫ j a = p₂ ≫ j b := by
      ext
      simp [p₁, p₂, pullback.condition]
    have key : p₁ ≫ fU a = p₂ ≫ fU b := by
      rw [over_hom_eq_iff_forall_field_algebra]
      intro k _ _ x
      rw [← Category.assoc, ← Category.assoc, hfU, hfU, Category.assoc, Category.assoc, hp]
    simpa [p₁, p₂] using congrArg CommaMorphism.left key
  let g₀ : T.left ⟶ Y.left := 𝒰.glueMorphisms (fun t ↦ (fU t).left) hcomp
  have hg : ∀ t, (j t).left ≫ g₀ = (fU t).left := fun t ↦ 𝒰.ι_glueMorphisms _ hcomp t
  have hw : g₀ ≫ Y.hom = T.hom := by
    refine 𝒰.hom_ext _ _ fun t ↦ ?_
    change (j t).left ≫ g₀ ≫ Y.hom = (j t).left ≫ T.hom
    rw [← Category.assoc, hg, Over.w, Over.w]
  refine ⟨Over.homMk g₀ hw, fun k _ _ x ↦ ?_⟩
  set t := x.left (IsLocalRing.closedPoint k) with ht
  have := hj t
  have hr : Set.range x.left ⊆ Set.range (j t).left := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim (α := ↥(Spec (CommRingCat.of k))) p (IsLocalRing.closedPoint k)]
    exact hmem t
  let y₀ : Spec (.of k) ⟶ (U t).left := IsOpenImmersion.lift (j t).left x.left hr
  have hy₀ : y₀ ≫ (j t).left = x.left := IsOpenImmersion.lift_fac _ _ _
  let y : specOver R k ⟶ U t := Over.homMk y₀ (by
    rw [← Over.w (j t), ← Category.assoc, hy₀, Over.w])
  have hxy : x = y ≫ j t := by
    ext
    simp [y, hy₀]
  have hjt : j t ≫ Over.homMk g₀ hw = fU t := by
    ext
    simp [hg]
  rw [hxy, Category.assoc, hjt, hfU]

end Glue

section Pullback

variable {S S' : Scheme.{u}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def pullbackPointEquiv (h : IsPullback φ G'.hom G.hom f) (T : Over S') :
    (T ⟶ G') ≃ ((Over.map f).obj T ⟶ G) where
  toFun x := Over.homMk (x.left ≫ φ) (by
    change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.w, Over.w_assoc])
  invFun y := Over.homMk (h.lift y.left T.hom (Over.w y)) (h.lift_snd ..)
  left_inv x := Over.OverMorphism.ext (h.hom_ext (h.lift_fst ..)
    ((h.lift_snd ..).trans (Over.w x).symm))
  right_inv y := Over.OverMorphism.ext (h.lift_fst ..)

@[simp] theorem pullbackPointEquiv_apply_left (h : IsPullback φ G'.hom G.hom f) {T : Over S'}
    (x : T ⟶ G') : (pullbackPointEquiv h T x).left = x.left ≫ φ := rfl

def pullbackRepresentableBy [GrpObj G] (h : IsPullback φ G'.hom G.hom f) :
    (((Over.map f).op ⋙ yonedaGrpObj G) ⋙ forget _).RepresentableBy G' where
  homEquiv {T} := pullbackPointEquiv h T
  homEquiv_comp _ _ := Over.OverMorphism.ext (Category.assoc _ _ _)

@[instance_reducible]
def grpObjOfIsPullback [GrpObj G] (h : IsPullback φ G'.hom G.hom f) : GrpObj G' :=
  GrpObj.ofRepresentableBy G' _ (pullbackRepresentableBy h)

theorem pullbackPointEquiv_mul [GrpObj G] (h : IsPullback φ G'.hom G.hom f) {T : Over S'}
    (x y : T ⟶ G') :
    letI := grpObjOfIsPullback h
    pullbackPointEquiv h T (x * y) = pullbackPointEquiv h T x * pullbackPointEquiv h T y := by
  exact ((yonedaGrpObjIsoOfRepresentableBy G' _ (pullbackRepresentableBy h)).hom.app
    (Opposite.op T)).hom.map_mul x y

theorem isCommMonObj_of_isPullback [GrpObj G] [IsCommMonObj G]
    (h : IsPullback φ G'.hom G.hom f) :
    letI := grpObjOfIsPullback h
    IsCommMonObj G' := by
  letI := grpObjOfIsPullback h
  letI : CommMonoid ((Over.map f).obj (G' ⊗ G') ⟶ G) := Hom.commMonoid
  refine ⟨(pullbackPointEquiv h _).injective ?_⟩
  have e1 : (β_ G' G').hom ≫ μ = snd G' G' * fst G' G' := by
    rw [Hom.mul_def]
    congr 1
  have e2 : (μ : G' ⊗ G' ⟶ G') = fst G' G' * snd G' G' := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  rw [e1, e2, pullbackPointEquiv_mul, pullbackPointEquiv_mul, mul_comm]

theorem mul_left_comp_of_pullbackPointEquiv_mul [GrpObj G] [GrpObj G']
    (h : IsPullback φ G'.hom G.hom f) {T' : Over S'} {T : Over S} (t : T'.left ⟶ T.left)
    {x' y' : T' ⟶ G'} {x y : T ⟶ G}
    (hm : pullbackPointEquiv h T' (x' * y') =
      pullbackPointEquiv h T' x' * pullbackPointEquiv h T' y')
    (hx : x'.left ≫ φ = t ≫ x.left) (hy : y'.left ≫ φ = t ≫ y.left) :
    (x' * y').left ≫ φ = t ≫ (x * y).left := by
  rw [← pullbackPointEquiv_apply_left h, hm, Hom.mul_def, Hom.mul_def,
    Over.comp_left, Over.comp_left, ← Category.assoc]
  congr 1
  ext
  · rw [Category.assoc]
    change (lift (pullbackPointEquiv h T' x') (pullbackPointEquiv h T' y') ≫ fst G G).left = t ≫ (lift x y ≫ fst G G).left
    rw [lift_fst, lift_fst, pullbackPointEquiv_apply_left, hx]
  · rw [Category.assoc]
    change (lift (pullbackPointEquiv h T' x') (pullbackPointEquiv h T' y') ≫ snd G G).left = t ≫ (lift x y ≫ snd G G).left
    rw [lift_snd, lift_snd, pullbackPointEquiv_apply_left, hy]

end Pullback

section FieldPoints

variable {R : Type u} [CommRing R] {G : Over (Spec (.of R))}

@[instance_reducible]
def grpObjOfFieldPoints [IsSeparated G.hom] [IsReduced G.left] [IsReduced ((G ⊗ G) ⊗ G).left]
    (e : 𝟙_ _ ⟶ G) (m : G ⊗ G ⟶ G) (i : G ⟶ G)
    (H : ∀ (k : Type u) [Field k] [Algebra R k], ∃ (M : Type u) (_ : AddCommGroup M)
      (c : M ≃ (specOver R k ⟶ G)), toUnit _ ≫ e = c 0 ∧
        (∀ a b, lift (c a) (c b) ≫ m = c (a + b)) ∧ ∀ a, c a ≫ i = c (-a)) : GrpObj G where
  one := e
  mul := m
  inv := i
  one_mul :=
    have : IsIso (λ_ G).hom.left := ((Over.forget _).mapIso (λ_ G)).isIso_hom
    have : IsReduced (𝟙_ _ ⊗ G).left := isReduced_of_isOpenImmersion (λ_ G).hom.left
    over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => by
    obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
    obtain ⟨a, ha⟩ := c.surjective (x ≫ snd _ _)
    obtain rfl : x = lift (toUnit _) (c a) :=
      CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by simp [ha])
    simp [h₀, h₁]
  mul_one :=
    have : IsIso (ρ_ G).hom.left := ((Over.forget _).mapIso (ρ_ G)).isIso_hom
    have : IsReduced (G ⊗ 𝟙_ _).left := isReduced_of_isOpenImmersion (ρ_ G).hom.left
    over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => by
    obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
    obtain ⟨a, ha⟩ := c.surjective (x ≫ fst _ _)
    obtain rfl : x = lift (c a) (toUnit _) :=
      CartesianMonoidalCategory.hom_ext _ _ (by simp [ha]) (toUnit_unique _ _)
    simp [h₀, h₁]
  mul_assoc := over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => by
    obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
    obtain ⟨a, ha⟩ := c.surjective (x ≫ fst _ _ ≫ fst _ _)
    obtain ⟨b, hb⟩ := c.surjective (x ≫ fst _ _ ≫ snd _ _)
    obtain ⟨d, hd⟩ := c.surjective (x ≫ snd _ _)
    obtain rfl : x = lift (lift (c a) (c b)) (c d) := by ext <;> simp [ha, hb, hd]
    simp [h₁, add_assoc]
  left_inv := over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => by
    obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
    obtain ⟨a, rfl⟩ := c.surjective x
    simp [comp_lift_assoc, h₀, h₁, h₂]
  right_inv := over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => by
    obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
    obtain ⟨a, rfl⟩ := c.surjective x
    simp [comp_lift_assoc, h₀, h₁, h₂]

end FieldPoints

end GlobalTheory

import Mathlib

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

abbrev str : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

def Good (r : ℕ) {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) : Prop :=
  IsFinite (I.subschemeι ≫ pullback.snd _ g) ∧ Flat (I.subschemeι ≫ pullback.snd _ g) ∧
    ∀ y, (I.subschemeι ≫ pullback.snd _ g).finrank y = r

abbrev bc {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) :
    pullback (str A B) (a ≫ g) ⟶ pullback (str A B) g :=
  pullback.map _ _ _ _ (𝟙 _) a (𝟙 _) (by simp) (by simp)

theorem isPullback_bc {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) :
    IsPullback (bc A B g a) (pullback.snd _ (a ≫ g)) (pullback.snd _ g) a :=
  by
    have h : bc A B g a ≫ pullback.fst (str A B) g = pullback.fst _ _ :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [h]
    exact IsPullback.of_hasPullback (str A B) (a ≫ g)

theorem good_comap (r : ℕ) {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T)
    (I : (pullback (str A B) g).IdealSheafData) (hI : Good A B r g I) :
    Good A B r (a ≫ g) (I.comap (bc A B g a)) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have H : IsPullback (pullback.snd (bc A B g a) I.subschemeι)
      (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) I.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have e : (I.comap (bc A B g a)).subschemeι ≫ pullback.snd _ (a ≫ g) =
      (I.comapIso (bc A B g a)).hom ≫ (pullback.fst (bc A B g a) I.subschemeι ≫
        pullback.snd _ (a ≫ g)) := by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have f1 : IsFinite (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H h1
  have f2 : Flat (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @Flat) H h2
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [e]; infer_instance
  · rw [e]; infer_instance
  · rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ H y, h3]

theorem sigma_eq (r : ℕ) {T : Scheme.{0}} {g₀ g : T ⟶ Spec (CommRingCat.of A)} (h : g₀ = g)
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I : (pullback (str A B) g).IdealSheafData}
    (hI : I₀ = I.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])))
    (h₀ : Good A B r g₀ I₀) (h₁ : Good A B r g I) :
    (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g, ⟨I, h₁⟩⟩ := by
  subst h
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id] at hI
  subst hI
  rfl

theorem comap_bc_comp {T T' T'' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T)
    (b : T'' ⟶ T') (I : (pullback (str A B) g).IdealSheafData) :
    I.comap (bc A B g (b ≫ a)) = ((I.comap (bc A B g a)).comap (bc A B (a ≫ g) b)).comap
      (pullback.map (str A B) ((b ≫ a) ≫ g) (str A B) (b ≫ a ≫ g) (𝟙 _) (𝟙 _) (𝟙 _)
        (by simp) (by simp)) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  apply pullback.hom_ext <;>
    simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]

def functor (r : ℕ) : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := Σ g : T.unop ⟶ Spec (CommRingCat.of A),
    {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}
  map {_ _} a := TypeCat.ofHom fun x => ⟨a.unop ≫ x.1, ⟨x.2.1.comap (bc A B x.1 a.unop),
    good_comap A B r x.1 a.unop x.2.1 x.2.2⟩⟩
  map_id T := by
    ext x : 3
    exact sigma_eq A B r (Category.id_comp _) rfl _ _
  map_comp {T T' T''} a b := by
    ext x : 3
    exact sigma_eq A B r (Category.assoc _ _ _) (comap_bc_comp A B x.1 a.unop b.unop x.2.1) _ _

theorem functor_map (r : ℕ) {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    (functor A B r).map a.op y =
      ⟨a ≫ y.1, ⟨y.2.1.comap (bc A B y.1 a), good_comap A B r y.1 a y.2.1 y.2.2⟩⟩ := rfl

def Basic {r N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : Prop :=
  ∀ U : T.affineOpens, Function.Bijective fun c : Fin r → Γ(T, U) =>
    ∑ k, ((y.2.1.subschemeι ≫ pullback.snd _ y.1).app U).hom (c k) *
      ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤
        ((y.2.1.subschemeι ≫ pullback.snd _ y.1) ⁻¹ᵁ U) (by simp)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (e (σ k)))

end GlobalTheory.HilbAff

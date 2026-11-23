import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh

namespace FubiniStudyChowHeightFormula₂.Adr

universe v u v' u'

def Acyc (R : Type) [CommRing R] (D : Type u) [Category.{v} D] : Prop :=
  Nonempty D ∧ ∀ M : CommAlgCat.{0} R, (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a b, g a = g b) ∧
    (∀ c : H1 ((Functor.const D).obj M), c = 0) ∧ ∀ c : H2 ((Functor.const D).obj M), c = 0

section Contract

variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D]

def cm (M : CommAlgCat.{0} R) (G : D ⥤ D) :
    CoefMap (RingHom.id R) ((Functor.const D).obj M) ((Functor.const D).obj M) where
  G := G
  α _ := RingHom.id M
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem cm_zigzag (M : CommAlgCat.{0} R) {G G' : D ⥤ D} (h : Zigzag G G') :
    (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a, g (G.obj a) = g (G'.obj a)) ∧
    (∀ c, (cm M G).pull1 c = (cm M G').pull1 c) ∧ ∀ c, (cm M G).pull2 c = (cm M G').pull2 c := by
  have one : ∀ {G G' : D ⥤ D} (_ : G ⟶ G'),
      (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a, g (G.obj a) = g (G'.obj a)) ∧
      (∀ c, (cm M G).pull1 c = (cm M G').pull1 c) ∧ ∀ c, (cm M G).pull2 c = (cm M G').pull2 c :=
    fun {G G'} θ ↦ ⟨fun g hg a ↦ (hg _ _ (θ.app a)).symm,
      (cm M G).pullCohomologyOne_eq_of_natTrans (cm M G') θ fun _ _ ↦ rfl,
      (cm M G).pullCohomologyTwo_eq_of_natTrans (cm M G') θ fun _ _ ↦ rfl⟩
  induction h with
  | refl => exact ⟨fun _ _ _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  | tail _ hz ih =>
    rcases hz with ⟨⟨θ⟩⟩ | ⟨⟨θ⟩⟩
    · exact ⟨fun g hg a ↦ (ih.1 g hg a).trans ((one θ).1 g hg a), fun c ↦ (ih.2.1 c).trans ((one θ).2.1 c),
        fun c ↦ (ih.2.2 c).trans ((one θ).2.2 c)⟩
    · exact ⟨fun g hg a ↦ (ih.1 g hg a).trans ((one θ).1 g hg a).symm,
        fun c ↦ (ih.2.1 c).trans ((one θ).2.1 c).symm, fun c ↦ (ih.2.2 c).trans ((one θ).2.2 c).symm⟩

theorem acyc_of_zigzag (d : D) (h : Zigzag (𝟭 D) ((Functor.const D).obj d)) : Acyc R D := by
  refine ⟨⟨d⟩, fun M ↦ ?_⟩
  obtain ⟨h0, h1, h2⟩ := cm_zigzag M h
  refine ⟨fun g hg a b ↦ (h0 g hg a).trans (h0 g hg b).symm, fun c ↦ ?_, fun c ↦ ?_⟩
  · refine ((CoefMap.pullCohomologyOne_id c).symm.trans (h1 c)).trans ?_
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    refine ⟨0, ?_⟩
    rw [map_zero]
    funext T T' φ
    exact (Z1.id f d).symm
  · refine ((CoefMap.pullCohomologyTwo_id c).symm.trans (h2 c)).trans ?_
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    refine ⟨fun _ _ _ ↦ (z.1 d d d (𝟙 d) (𝟙 d) : M), ?_⟩
    funext T T' T'' φ ψ
    exact sub_add_cancel (z.1 d d d (𝟙 d) (𝟙 d) : M) (z.1 d d d (𝟙 d) (𝟙 d) : M)

theorem acyc_of_coprod (d : D) (P : D → D) (i : ∀ a, a ⟶ P a) (j : ∀ a, d ⟶ P a)
    (h : ∀ a b (φ : a ⟶ P b), ∃! ψ : P a ⟶ P b, i a ≫ ψ = φ ∧ j a ≫ ψ = j b) : Acyc R D := by
  choose m hm hu using h
  let Q : D ⥤ D :=
    { obj := P
      map := fun {a b} φ ↦ m a b (φ ≫ i b)
      map_id := fun a ↦ (hu a a _ (𝟙 _) ⟨by simp, by simp⟩).symm
      map_comp := fun {a b c} φ ψ ↦ (hu a c _ _ ⟨by
        rw [← Category.assoc, (hm a b _).1, Category.assoc, (hm b c _).1, Category.assoc], by
        rw [← Category.assoc, (hm a b _).2, (hm b c _).2]⟩).symm }
  let θ : 𝟭 D ⟶ Q := { app := i, naturality := fun a b φ ↦ (hm a b _).1.symm }
  let η : (Functor.const D).obj d ⟶ Q :=
    { app := j, naturality := fun a b φ ↦ (Category.id_comp _).trans (hm a b _).2.symm }
  exact acyc_of_zigzag d ((Zigzag.of_hom θ).trans (Zigzag.of_inv η))

end Contract

section Comma

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {G : C' ⥤ C} {T : C}

theorem Acyc.zero (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R) (g : ∀ S, (G.obj S ⟶ T) → M)
    (hg : ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T), g S (G.map ψ ≫ c) = g S' c) : ∃ m, ∀ S c, g S c = m := by
  obtain ⟨⟨a⟩, h⟩ := h
  refine ⟨g a.left a.hom, fun S c ↦ (h M).1 (fun b ↦ g b.left b.hom) (fun b b' φ ↦ ?_) (CostructuredArrow.mk c) a⟩
  exact (hg _ _ φ.left b'.hom).symm.trans (congrArg _ (CostructuredArrow.w φ))

theorem Acyc.one (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R)
    (f : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M)
    (hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
      f S S'' (φ ≫ ψ) c = f S S' φ (G.map ψ ≫ c) + f S' S'' ψ c) :
    ∃ v : ∀ S, (G.obj S ⟶ T) → M, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T), f S S' ψ c = v S' c - v S (G.map ψ ≫ c) := by
  let f' : Z1 ((Functor.const (CostructuredArrow G T)).obj M) :=
    ⟨fun a b φ ↦ (f a.left b.left φ.left b.hom : M), fun a b c φ ψ ↦
      (hf _ _ _ φ.left ψ.left c.hom).trans
        (congrArg (fun t ↦ f _ _ φ.left t + f _ _ ψ.left c.hom) (CostructuredArrow.w ψ))⟩
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 ((h.2 M).2.1 (H1.mk _ f'))
  exact ⟨fun S c ↦ g (CostructuredArrow.mk c), fun S S' ψ c ↦
    (congrFun (congrFun (congrFun hg (CostructuredArrow.mk (G.map ψ ≫ c))) (CostructuredArrow.mk c))
      (CostructuredArrow.homMk ψ rfl)).symm⟩

theorem Acyc.two (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R)
    (z : ∀ S S' S'', (S ⟶ S') → (S' ⟶ S'') → (G.obj S'' ⟶ T) → M)
    (hz : ∀ S S' S'' S''' (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S'' ⟶ S''') (c : G.obj S''' ⟶ T),
      z S S' S'' φ ψ (G.map χ ≫ c) + z S S'' S''' (φ ≫ ψ) χ c = z S S' S''' φ (ψ ≫ χ) c + z S' S'' S''' ψ χ c) :
    ∃ w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M, ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
      z S S' S'' φ ψ c = w S S' φ (G.map ψ ≫ c) - w S S'' (φ ≫ ψ) c + w S' S'' ψ c := by
  let z' : Z2 ((Functor.const (CostructuredArrow G T)).obj M) :=
    ⟨fun a b c φ ψ ↦ (z a.left b.left c.left φ.left ψ.left c.hom : M), fun a b c e φ ψ χ ↦
      (congrArg (fun t ↦ z _ _ _ φ.left ψ.left t + z _ _ _ (φ.left ≫ ψ.left) χ.left e.hom)
        (CostructuredArrow.w χ)).symm.trans (hz _ _ _ _ φ.left ψ.left χ.left e.hom)⟩
  obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 ((h.2 M).2.2 (H2.mk _ z'))
  let w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M := fun S S' ψ c ↦
    g (CostructuredArrow.mk (G.map ψ ≫ c)) (CostructuredArrow.mk c) (CostructuredArrow.homMk ψ rfl)
  have hw : ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T) (c₀ : G.obj S ⟶ T) (e : G.map ψ ≫ c = c₀),
      (g (CostructuredArrow.mk c₀) (CostructuredArrow.mk c) (CostructuredArrow.homMk ψ e) : M) = w S S' ψ c := by
    intro S S' ψ c c₀ e
    subst e
    rfl
  refine ⟨w, fun S S' S'' φ ψ c ↦ ?_⟩
  have k := congrFun (congrFun (congrFun (congrFun (congrFun hg
    (CostructuredArrow.mk (G.map φ ≫ G.map ψ ≫ c))) (CostructuredArrow.mk (G.map ψ ≫ c))) (CostructuredArrow.mk c))
      (CostructuredArrow.homMk φ rfl)) (CostructuredArrow.homMk ψ rfl)
  rw [← hw S S'' (φ ≫ ψ) c (G.map φ ≫ G.map ψ ≫ c) (by simp)]
  exact k.symm

end Comma

section QA

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

theorem qa1 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (h : ∀ T, Acyc R (CostructuredArrow G T)) :
    Function.Bijective (CoefMap.restrict F G).pull1 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let g' : ∀ S, F.obj (G.obj S) := g
    have hg' : ∀ S S' (ψ : S ⟶ S'), f.1 _ _ (G.map ψ) = g' S' - mp F (G.map ψ) (g' S) := fun S S' ψ ↦
      (congrFun (congrFun (congrFun hg S) S') ψ).symm
    have ex : ∀ T, ∃ m : F.obj T, ∀ S (c : G.obj S ⟶ T), f.1 _ _ c + mp F c (g' S) = m := fun T ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        simp only [Z1.comp f, hg', mp_comp, map_sub]; ring
    choose m hm using ex
    refine H1.mk_eq_zero.2 ⟨m, ?_⟩
    funext T T' φ
    obtain ⟨a⟩ := (h T).1
    let c : G.obj a.left ⟶ T := a.hom
    rw [amitsur_d0_apply, ← hm T _ c, ← hm T' _ (c ≫ φ)]
    simp only [Z1.comp f, mp_comp, map_add]; ring
  · intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    let f' : ∀ S S', (S ⟶ S') → F.obj (G.obj S') := f.1
    have hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S''),
        f' S S'' (φ ≫ ψ) = mp F (G.map ψ) (f' S S' φ) + f' S' S'' ψ := fun S S' S'' φ ψ ↦ f.2 φ ψ
    have ex : ∀ T, ∃ v : ∀ S, (G.obj S ⟶ T) → F.obj T, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        -mp F c (f' S S' ψ) = v S' c - v S (G.map ψ ≫ c) := fun T ↦
      (h T).one _ (fun S S' ψ c ↦ -mp F c (f' S S' ψ)) fun S S' S'' φ ψ c ↦ by
        simp only [hf, mp_comp, map_add]; ring
    choose v hv using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ m : F.obj T', ∀ S (c : G.obj S ⟶ T),
        v T' S (c ≫ φ) - mp F φ (v T S c) = m := fun T T' φ ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e1 := hv T' S S' ψ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hv T S S' ψ c)
        simp only [mp_comp, map_sub, map_neg, Category.assoc] at e1 e2 ⊢
        linear_combination e1 - e2
    choose m hm using ex
    refine ⟨H1.mk _ ⟨m, fun T T' T'' φ ψ ↦ ?_⟩, ?_⟩
    · obtain ⟨a⟩ := (h T).1
      let c : G.obj a.left ⟶ T := a.hom
      rw [← hm T T'' _ _ c, ← hm T T' _ _ c, ← hm T' T'' _ _ (c ≫ φ)]
      simp only [mp_comp, map_sub, Category.assoc]; ring
    · rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
      refine ⟨fun S ↦ v _ S (𝟙 _), ?_⟩
      funext S S' ψ
      have e1 := hm _ _ (G.map ψ) S (𝟙 _)
      have e2 := hv _ S S' ψ (𝟙 _)
      rw [Category.id_comp] at e1
      rw [Category.comp_id, mp_id] at e2
      change v _ S' (𝟙 _) - mp F (G.map ψ) (v _ S (𝟙 _)) = m _ _ (G.map ψ) - f' S S' ψ
      linear_combination e1 - e2

theorem qa2 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (h : ∀ T, Acyc R (CostructuredArrow G T)) :
    Function.Bijective (CoefMap.restrict F G).pull2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let f : ∀ S S', (S ⟶ S') → F.obj (G.obj S') := g
    have hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S''), z.1 _ _ _ (G.map φ) (G.map ψ) =
        mp F (G.map ψ) (f S S' φ) - f S S'' (φ ≫ ψ) + f S' S'' ψ := fun S S' S'' φ ψ ↦
      (congrFun (congrFun (congrFun (congrFun (congrFun hg S) S') S'') φ) ψ).symm
    have ex : ∀ T, ∃ v : ∀ S, (G.obj S ⟶ T) → F.obj T, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        z.1 _ _ _ (G.map ψ) c - mp F c (f S S' ψ) = v S' c - v S (G.map ψ ≫ c) := fun T ↦
      (h T).one _ (fun S S' ψ c ↦ z.1 _ _ _ (G.map ψ) c - mp F c (f S S' ψ)) fun S S' S'' φ ψ c ↦ by
        have e := z.2 (G.map φ) (G.map ψ) c
        simp only [hf, mp_comp, map_add, map_sub, Functor.map_comp] at e ⊢
        linear_combination e
    choose v hv using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ m : F.obj T', ∀ S (c : G.obj S ⟶ T),
        z.1 _ _ _ c φ - mp F φ (v T S c) + v T' S (c ≫ φ) = m := fun T T' φ ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e := z.2 (G.map ψ) c φ
        have e1 := hv T' S S' ψ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hv T S S' ψ c)
        simp only [mp_comp, map_sub, Category.assoc] at e1 e2 ⊢
        linear_combination e + e1 - e2
    choose m hm using ex
    refine H2.mk_eq_zero.2 ⟨m, ?_⟩
    funext T T' T'' φ ψ
    obtain ⟨a⟩ := (h T).1
    let c : G.obj a.left ⟶ T := a.hom
    have e := z.2 c φ ψ
    rw [d1_apply, ← hm T T'' _ _ c, ← hm T T' _ _ c, ← hm T' T'' _ _ (c ≫ φ)]
    simp only [mp_comp, map_sub, map_add, Category.assoc]
    linear_combination e
  · intro c
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    let y : ∀ S S' S'', (S ⟶ S') → (S' ⟶ S'') → F.obj (G.obj S'') := z.1
    have hy : ∀ S S' S'' S''' (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S'' ⟶ S'''),
        mp F (G.map χ) (y _ _ _ φ ψ) + y _ _ _ (φ ≫ ψ) χ = y _ _ _ φ (ψ ≫ χ) + y _ _ _ ψ χ :=
      fun S S' S'' S''' φ ψ χ ↦ z.2 φ ψ χ
    have ex : ∀ T, ∃ w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → F.obj T,
        ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
          mp F c (y _ _ _ φ ψ) = w S S' φ (G.map ψ ≫ c) - w S S'' (φ ≫ ψ) c + w S' S'' ψ c := fun T ↦
      (h T).two _ (fun S S' S'' φ ψ c ↦ mp F c (y _ _ _ φ ψ)) fun S S' S'' S''' φ ψ χ c ↦ by
        simp only [mp_comp, ← map_add, hy]
    choose w hw using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ x : ∀ S, (G.obj S ⟶ T) → F.obj T', ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        mp F φ (w T S S' ψ c) - w T' S S' ψ (c ≫ φ) = x S' c - x S (G.map ψ ≫ c) := fun T T' φ ↦
      (h T).one _ (fun S S' ψ c ↦ mp F φ (w T S S' ψ c) - w T' S S' ψ (c ≫ φ)) fun S S' S'' ψ χ c ↦ by
        have e1 := hw T' S S' S'' ψ χ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hw T S S' S'' ψ χ c)
        simp only [mp_comp, map_sub, map_add, Category.assoc] at e1 e2 ⊢
        linear_combination e2 - e1
    choose x hx using ex
    have ex : ∀ T T' T'' (φ : T ⟶ T') (φ' : T' ⟶ T''), ∃ m : F.obj T'', ∀ S (c : G.obj S ⟶ T),
        mp F φ' (x T T' φ S c) + x T' T'' φ' S (c ≫ φ) - x T T'' (φ ≫ φ') S c = m := fun T T' T'' φ φ' ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e1 := congrArg (mp F φ') (hx T T' φ S S' ψ c)
        have e2 := hx T' T'' φ' S S' ψ (c ≫ φ)
        have e3 := hx T T'' (φ ≫ φ') S S' ψ c
        simp only [mp_comp, map_sub, Category.assoc] at e1 e2 e3 ⊢
        linear_combination e1 + e2 - e3
    choose m hm using ex
    refine ⟨H2.mk _ ⟨m, fun T T' T'' T''' φ ψ χ ↦ ?_⟩, ?_⟩
    · obtain ⟨a⟩ := (h T).1
      let c : G.obj a.left ⟶ T := a.hom
      rw [← hm T T' T'' _ _ _ c, ← hm T T'' T''' _ _ _ c, ← hm T T' T''' _ _ _ c, ← hm T' T'' T''' _ _ _ (c ≫ φ)]
      simp only [mp_comp, map_sub, map_add, Category.assoc]; ring
    · rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
      refine ⟨fun S S' ψ ↦ x _ _ (G.map ψ) S (𝟙 _) - w _ S S' ψ (𝟙 _), ?_⟩
      funext S S' S'' φ ψ
      have e1 := hm _ _ _ (G.map φ) (G.map ψ) S (𝟙 _)
      have e2 := hw _ S S' S'' φ ψ (𝟙 _)
      have e3 := hx _ _ (G.map ψ) S S' φ (𝟙 _)
      rw [Category.id_comp] at e1 e3
      rw [Category.comp_id] at e2 e3
      rw [mp_id] at e2
      change mp F (G.map ψ) (x _ _ (G.map φ) S (𝟙 _) - w _ S S' φ (𝟙 _)) -
        (x _ _ (G.map (φ ≫ ψ)) S (𝟙 _) - w _ S S'' (φ ≫ ψ) (𝟙 _)) + (x _ _ (G.map ψ) S' (𝟙 _) - w _ S' S'' ψ (𝟙 _)) =
        m _ _ _ (G.map φ) (G.map ψ) - y _ _ _ φ ψ
      rw [map_sub, G.map_comp]
      linear_combination e1 + e2 - e3

end QA

end FubiniStudyChowHeightFormula₂.Adr

import Mathlib

universe w' v u

open CategoryTheory Limits Abelian Opposite

noncomputable section

namespace GlobalTheory

namespace SheafLES

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}]

variable (J) in

abbrev freeYoneda : C ⥤ Sheaf J AddCommGrpCat.{v} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf _ _

def freeYonedaHomEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeYoneda J).obj U ⟶ F) ≃ F.obj.obj (op U) :=
  (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F).trans
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.obj)).trans yonedaEquiv

def tautSection (U : C) : ((freeYoneda J).obj U).obj.obj (op U) :=
  freeYonedaHomEquiv U _ (𝟙 _)

lemma freeYonedaHomEquiv_comp (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeYoneda J).obj U ⟶ F) (f : F ⟶ G) :
    freeYonedaHomEquiv U G (φ ≫ f) = f.hom.app (op U) (freeYonedaHomEquiv U F φ) := rfl

lemma freeYonedaHomEquiv_apply (U : C) {F : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeYoneda J).obj U ⟶ F) :
    freeYonedaHomEquiv U F φ = φ.hom.app (op U) (tautSection U) := by
  rw [tautSection, ← freeYonedaHomEquiv_comp, Category.id_comp]

lemma freeYonedaHomEquiv_map_comp {U V : C} (i : V ⟶ U) {F : Sheaf J AddCommGrpCat.{v}}
    (φ : (freeYoneda J).obj U ⟶ F) :
    freeYonedaHomEquiv V F ((freeYoneda J).map i ≫ φ) =
      F.obj.map i.op (freeYonedaHomEquiv U F φ) := by
  have h1 := (sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv_naturality_left
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map i)) φ
  have h2 := (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left (yoneda.map i)
    ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F φ)
  have h3 := yonedaEquiv_naturality
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) F.obj
      ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ F φ)) i
  refine Eq.trans ?_ h3.symm
  exact congrArg yonedaEquiv ((congrArg
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj V) F.obj) h1).trans h2)

def freeYonedaHomAddEquiv (U : C) (F : Sheaf J AddCommGrpCat.{v}) :
    ((freeYoneda J).obj U ⟶ F) ≃+ F.obj.obj (op U) where
  toEquiv := freeYonedaHomEquiv U F
  map_add' φ ψ := by
    change freeYonedaHomEquiv U F (φ + ψ) = freeYonedaHomEquiv U F φ + freeYonedaHomEquiv U F ψ
    simp only [freeYonedaHomEquiv_apply]
    rfl

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

section Basic

variable {F G K : Sheaf J AddCommGrpCat.{v}}

def map (f : F ⟶ G) (n : ℕ) (U : C) : Sheaf.H'.{w'} F n U →+ Sheaf.H'.{w'} G n U :=
  (((Sheaf.cohomologyPresheafFunctor.{w'} J n).map f).app (op U)).hom

def res (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {U V : C} (i : V ⟶ U) :
    Sheaf.H'.{w'} F n U →+ Sheaf.H'.{w'} F n V :=
  ((Sheaf.cohomologyPresheaf.{w'} F n).map i.op).hom

lemma map_apply (f : F ⟶ G) (n : ℕ) (U : C) (x : Ext.{w'} ((freeYoneda J).obj U) F n) :
    map f n U x = x.comp (Ext.mk₀ f) (add_zero n) := rfl

lemma res_apply (n : ℕ) {U V : C} (i : V ⟶ U) (x : Ext.{w'} ((freeYoneda J).obj U) F n) :
    res F n i x = (Ext.mk₀ ((freeYoneda J).map i)).comp x (zero_add n) := rfl

@[simp] lemma map_id (n : ℕ) (U : C) (x : Sheaf.H'.{w'} F n U) : map (𝟙 F) n U x = x :=
  Ext.comp_mk₀_id (X := (freeYoneda J).obj U) x

lemma map_comp (f : F ⟶ G) (g : G ⟶ K) (n : ℕ) (U : C) (x : Sheaf.H'.{w'} F n U) :
    map (f ≫ g) n U x = map g n U (map f n U x) := by
  have (y : Ext.{w'} ((freeYoneda J).obj U) F n) : y.comp (Ext.mk₀ (f ≫ g)) (add_zero n) =
      (y.comp (Ext.mk₀ f) (add_zero n)).comp (Ext.mk₀ g) (add_zero n) := by simp
  exact this x

@[simp] lemma map_zero_hom (n : ℕ) (U : C) (x : Sheaf.H'.{w'} F n U) :
    map (0 : F ⟶ G) n U x = 0 := by
  have (y : Ext.{w'} ((freeYoneda J).obj U) F n) :
      y.comp (Ext.mk₀ (0 : F ⟶ G)) (add_zero n) = 0 := by simp
  exact this x

lemma map_add_hom (f g : F ⟶ G) (n : ℕ) (U : C) (x : Sheaf.H'.{w'} F n U) :
    map (f + g) n U x = map f n U x + map g n U x := by
  have (y : Ext.{w'} ((freeYoneda J).obj U) F n) :
      y.comp (Ext.mk₀ (f + g)) (add_zero n) =
        y.comp (Ext.mk₀ f) (add_zero n) + y.comp (Ext.mk₀ g) (add_zero n) := by
    simp [Ext.mk₀_add]
  exact this x

@[simp] lemma res_id (n : ℕ) (U : C) (x : Sheaf.H'.{w'} F n U) : res F n (𝟙 U) x = x := by
  simp [res]

lemma res_comp (n : ℕ) {U V W : C} (i : V ⟶ U) (j : W ⟶ V) (x : Sheaf.H'.{w'} F n U) :
    res F n (j ≫ i) x = res F n j (res F n i x) := by
  simp [res]

lemma res_map (f : F ⟶ G) (n : ℕ) {U V : C} (i : V ⟶ U) (x : Sheaf.H'.{w'} F n U) :
    res G n i (map f n U x) = map f n V (res F n i x) :=
  (ConcreteCategory.congr_hom
    (((Sheaf.cohomologyPresheafFunctor.{w'} J n).map f).naturality i.op) x).symm

def equivZero (F : Sheaf J AddCommGrpCat.{v}) (U : C) :
    Sheaf.H'.{w'} F 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀ (X := (freeYoneda J).obj U) (Y := F)).trans (freeYonedaHomAddEquiv U F)

lemma equivZero_mk₀ (U : C) (φ : (freeYoneda J).obj U ⟶ F) :
    equivZero.{w'} F U (Ext.mk₀ φ) = freeYonedaHomEquiv U F φ := by
  have : Ext.addEquiv₀.{w'} (Ext.mk₀ φ) = φ := by
    apply (Ext.mk₀_bijective _ _).injective
    simp
  exact congrArg (freeYonedaHomEquiv U F) this

lemma equivZero_map (f : F ⟶ G) (U : C) (x : Sheaf.H'.{w'} F 0 U) :
    equivZero G U (map f 0 U x) = f.hom.app (op U) (equivZero F U x) := by
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective ((freeYoneda J).obj U) F).surjective x
  rw [map_apply, Ext.mk₀_comp_mk₀, equivZero_mk₀, equivZero_mk₀, freeYonedaHomEquiv_comp]

lemma equivZero_res {U V : C} (i : V ⟶ U) (x : Sheaf.H'.{w'} F 0 U) :
    equivZero F V (res F 0 i x) = F.obj.map i.op (equivZero F U x) := by
  obtain ⟨φ, rfl⟩ := (Ext.mk₀_bijective ((freeYoneda J).obj U) F).surjective x
  rw [res_apply, Ext.mk₀_comp_mk₀, equivZero_mk₀, equivZero_mk₀, freeYonedaHomEquiv_map_comp]

lemma map_equivZero_symm (f : F ⟶ G) (U : C) (s : F.obj.obj (op U)) :
    map f 0 U ((equivZero.{w'} F U).symm s) = (equivZero G U).symm (f.hom.app (op U) s) := by
  apply (equivZero G U).injective
  rw [equivZero_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

end Basic

section Sequence

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{v})} (hS : S.ShortExact)

def δ (n : ℕ) (U : C) : Sheaf.H'.{w'} S.X₃ n U →+ Sheaf.H'.{w'} S.X₁ (n + 1) U :=
  hS.extClass.postcomp ((freeYoneda J).obj U) rfl

lemma δ_apply (n : ℕ) (U : C) (x : Ext.{w'} ((freeYoneda J).obj U) S.X₃ n) :
    δ hS n U x = x.comp hS.extClass rfl := rfl

include hS in

theorem exact₂ (n : ℕ) (U : C) : Function.Exact (map.{w'} S.f n U) (map.{w'} S.g n U) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₂' ((freeYoneda J).obj U) hS n)

theorem exact₃ (n : ℕ) (U : C) : Function.Exact (map.{w'} S.g n U) (δ.{w'} hS n U) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₃' ((freeYoneda J).obj U) hS n (n + 1) rfl)

theorem exact₁ (n : ℕ) (U : C) : Function.Exact (δ.{w'} hS n U) (map.{w'} S.f (n + 1) U) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₁' ((freeYoneda J).obj U) hS n (n + 1) rfl)

theorem map_zero_injective_of_mono {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) [Mono f]
    (U : C) : Function.Injective (map.{w'} f 0 U) :=
  Ext.postcomp_mk₀_injective_of_mono ((freeYoneda J).obj U) f

include hS in

theorem injective_zero (U : C) : Function.Injective (map.{w'} S.f 0 U) :=
  have := hS.mono_f
  map_zero_injective_of_mono S.f U

@[simp] lemma δ_map (n : ℕ) (U : C) (x : Sheaf.H'.{w'} S.X₂ n U) :
    δ hS n U (map S.g n U x) = 0 :=
  (exact₃ hS n U).apply_apply_eq_zero x

@[simp] lemma map_δ (n : ℕ) (U : C) (x : Sheaf.H'.{w'} S.X₃ n U) :
    map S.f (n + 1) U (δ hS n U x) = 0 :=
  (exact₁ hS n U).apply_apply_eq_zero x

theorem δ_naturality {S₁ S₂ : ShortComplex (Sheaf J AddCommGrpCat.{v})} (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n : ℕ) (U : C) (x : Sheaf.H'.{w'} S₁.X₃ n U) :
    map φ.τ₁ (n + 1) U (δ h₁ n U x) = δ h₂ n U (map φ.τ₃ n U x) := by
  have (y : Ext.{w'} ((freeYoneda J).obj U) S₁.X₃ n) :
      (y.comp h₁.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
        (y.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp h₂.extClass rfl := by
    rw [Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_second_deg_zero,
      ShortComplex.ShortExact.extClass_naturality h₁ h₂ φ]
  exact this x

theorem δ_res (n : ℕ) {U V : C} (i : V ⟶ U) (x : Sheaf.H'.{w'} S.X₃ n U) :
    res S.X₁ (n + 1) i (δ hS n U x) = δ hS n V (res S.X₃ n i x) := by
  have (y : Ext.{w'} ((freeYoneda J).obj U) S.X₃ n) :
      (Ext.mk₀ ((freeYoneda J).map i)).comp (y.comp hS.extClass rfl) (zero_add (n + 1)) =
        ((Ext.mk₀ ((freeYoneda J).map i)).comp y (zero_add n)).comp hS.extClass rfl :=
    (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm
  exact this x

include hS

theorem δ_equivZero_symm_eq_zero_iff (U : C) (s : S.X₃.obj.obj (op U)) :
    δ.{w'} hS 0 U ((equivZero S.X₃ U).symm s) = 0 ↔ ∃ t, S.g.hom.app (op U) t = s := by
  rw [exact₃ hS 0 U]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨equivZero S.X₂ U x, by rw [← equivZero_map, hx, AddEquiv.apply_symm_apply]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨_, map_equivZero_symm S.g U t⟩

theorem sections_surjective_of_subsingleton (U : C)
    (h : Subsingleton (Sheaf.H'.{w'} S.X₁ 1 U)) : Function.Surjective (S.g.hom.app (op U)) :=
  fun s => (δ_equivZero_symm_eq_zero_iff.{w'} hS U s).1 (@Subsingleton.elim _ h _ _)

theorem δ_surjective_of_subsingleton (n : ℕ) (U : C)
    (h : Subsingleton (Sheaf.H'.{w'} S.X₂ (n + 1) U)) : Function.Surjective (δ.{w'} hS n U) :=
  fun x => ((exact₁ hS n U) x).1 (Subsingleton.elim _ _)

theorem δ_injective_of_subsingleton (n : ℕ) (U : C)
    (h : Subsingleton (Sheaf.H'.{w'} S.X₂ n U)) : Function.Injective (δ.{w'} hS n U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := ((exact₃ hS n U) x).1 hx
  rw [Subsingleton.elim y 0, map_zero]

theorem map_f_injective_of_surjective (n : ℕ) (U : C)
    (h : Function.Surjective (map.{w'} S.g n U)) :
    Function.Injective (map.{w'} S.f (n + 1) U) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := ((exact₁ hS n U) x).1 hx
  obtain ⟨z, rfl⟩ := h y
  exact δ_map hS n U z

theorem map_f_one_injective_of_sections_surjective (U : C)
    (h : Function.Surjective (S.g.hom.app (op U))) : Function.Injective (map.{w'} S.f 1 U) := by
  refine map_f_injective_of_surjective hS 0 U fun x => ?_
  obtain ⟨s, rfl⟩ := (equivZero S.X₃ U).symm.surjective x
  obtain ⟨t, rfl⟩ := h s
  exact ⟨_, map_equivZero_symm S.g U t⟩

theorem subsingleton₂ (n : ℕ) (U : C) (h₁ : Subsingleton (Sheaf.H'.{w'} S.X₁ n U))
    (h₃ : Subsingleton (Sheaf.H'.{w'} S.X₃ n U)) : Subsingleton (Sheaf.H'.{w'} S.X₂ n U) :=
  subsingleton_of_forall_eq 0 fun x => by
    obtain ⟨y, rfl⟩ := ((exact₂ hS n U) x).1 (Subsingleton.elim _ _)
    rw [Subsingleton.elim y 0, map_zero]

theorem subsingleton₃ (n : ℕ) (U : C) (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ n U))
    (h₁ : Subsingleton (Sheaf.H'.{w'} S.X₁ (n + 1) U)) : Subsingleton (Sheaf.H'.{w'} S.X₃ n U) :=
  (δ_injective_of_subsingleton hS n U h₂).subsingleton

theorem subsingleton₁ (n : ℕ) (U : C) (h₃ : Subsingleton (Sheaf.H'.{w'} S.X₃ n U))
    (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ (n + 1) U)) :
    Subsingleton (Sheaf.H'.{w'} S.X₁ (n + 1) U) :=
  (δ_surjective_of_subsingleton hS n U h₂).subsingleton

theorem subsingleton₁_zero (U : C) (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ 0 U)) :
    Subsingleton (Sheaf.H'.{w'} S.X₁ 0 U) :=
  (injective_zero hS U).subsingleton

theorem subsingleton₁_one_of_sections_surjective (U : C)
    (h : Function.Surjective (S.g.hom.app (op U)))
    (h₂ : Subsingleton (Sheaf.H'.{w'} S.X₂ 1 U)) : Subsingleton (Sheaf.H'.{w'} S.X₁ 1 U) :=
  (map_f_one_injective_of_sections_surjective hS U h).subsingleton

end Sequence

end Site

section Modules

universe v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

theorem toSheaf_preservesColimitsOfShape (K : Type*) [Category K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] :
    PreservesColimitsOfShape K (SheafOfModules.toSheaf.{v} R) where
  preservesColimit {F} := by
    let e : F ≅ (F ⋙ SheafOfModules.forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    have h1 : PreservesColimitsOfShape K (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙
        SheafOfModules.toSheaf.{v} R) :=
      inferInstanceAs (PreservesColimitsOfShape K
        (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat.{v}))
    have h2 : PreservesColimit
        ((F ⋙ SheafOfModules.forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj))
        (SheafOfModules.toSheaf.{v} R) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves (PresheafOfModules.sheafification.{v} (𝟙 R.obj))
          (colimit.isColimit (F ⋙ SheafOfModules.forget R)))
        (isColimitOfPreserves (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙
          SheafOfModules.toSheaf.{v} R) (colimit.isColimit (F ⋙ SheafOfModules.forget R)))
    exact preservesColimit_of_iso_diagram _ e.symm

instance toSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{v} R) where
  preservesFiniteColimits K _ _ := toSheaf_preservesColimitsOfShape R K

theorem shortExact_map_toSheaf {S : ShortComplex (SheafOfModules.{v} R)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf.{v} R)).ShortExact :=
  hS.map_of_exact _

end Modules

section Top

open TopologicalSpace

variable {X : TopCat.{u}}

end Top

section Scheme

open AlgebraicGeometry

variable (X : Scheme.{u})

def toAbSheaf : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  SheafOfModules.toSheaf X.ringCatSheaf

instance : (toAbSheaf X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive
instance : (toAbSheaf X).Faithful :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful
instance : (toAbSheaf X).ReflectsIsomorphisms :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).ReflectsIsomorphisms
instance : PreservesFiniteLimits (toAbSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))
instance : PreservesFiniteColimits (toAbSheaf X) :=
  inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf X.ringCatSheaf))

variable {X}

@[simp] lemma toAbSheaf_obj_obj (M : X.Modules) : ((toAbSheaf X).obj M).obj = M.presheaf := rfl

@[simp] lemma toAbSheaf_map_hom {M N : X.Modules} (φ : M ⟶ N) :
    ((toAbSheaf X).map φ).hom = φ.mapPresheaf := rfl

theorem shortExact_map_toAbSheaf {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toAbSheaf X)).ShortExact :=
  hS.map_of_exact _

theorem exact_map_toAbSheaf_iff (S : ShortComplex X.Modules) :
    (S.map (toAbSheaf X)).Exact ↔ S.Exact :=
  S.exact_map_iff_of_faithful _

end Scheme

end SheafLES

end GlobalTheory

import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapFOneInjectiveOfSectionsSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CohomologyPresheafFunctorMapAppApply

open CategoryTheory Abelian Opposite Limits TopologicalSpace

universe w w' w'' v u u₁ v₁ u₂ v₂

noncomputable section

namespace GlobalTheory

namespace SheafPull

section Abstract

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasExt.{w'} B]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

def extMap {Z F : A} {Z' G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G) (n : ℕ) :
    Ext.{w} Z F n →+ Ext.{w'} Z' G n :=
  ((Ext.mk₀ a).precomp G (zero_add n)).comp
    (((Ext.mk₀ b).postcomp (Φ.obj Z) (add_zero n)).comp (Φ.mapExtAddHom Z F n))

lemma extMap_apply {Z F : A} {Z' G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G) (n : ℕ)
    (x : Ext.{w} Z F n) :
    extMap.{w, w'} Φ a b n x = (Ext.mk₀ a).comp
      ((x.mapExactFunctor Φ).comp (Ext.mk₀ b) (add_zero n)) (zero_add n) := rfl

lemma extMap_mk₀ {Z F : A} {Z' G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G) (g : Z ⟶ F) :
    extMap.{w, w'} Φ a b 0 (Ext.mk₀ g) = Ext.mk₀ (a ≫ Φ.map g ≫ b) := by
  rw [extMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]

lemma extMap_comp_right {Z F F' : A} {Z' G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F' ⟶ G)
    (s : F ⟶ F') (n : ℕ) (x : Ext.{w} Z F n) :
    extMap.{w, w'} Φ a b n (x.comp (Ext.mk₀ s) (add_zero n)) =
      extMap.{w, w'} Φ a (Φ.map s ≫ b) n x := by
  simp only [extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

lemma comp_extMap_right {Z F : A} {Z' G G' : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G)
    (t : G ⟶ G') (n : ℕ) (x : Ext.{w} Z F n) :
    (extMap.{w, w'} Φ a b n x).comp (Ext.mk₀ t) (add_zero n) =
      extMap.{w, w'} Φ a (b ≫ t) n x := by
  simp only [extMap_apply, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

lemma extMap_comp_left {Z Z₁ F : A} {Z' G : B} (a : Z' ⟶ Φ.obj Z₁) (b : Φ.obj F ⟶ G)
    (s : Z₁ ⟶ Z) (n : ℕ) (x : Ext.{w} Z F n) :
    extMap.{w, w'} Φ a b n ((Ext.mk₀ s).comp x (zero_add n)) =
      extMap.{w, w'} Φ (a ≫ Φ.map s) b n x := by
  simp only [extMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc]

lemma comp_extMap_left {Z F : A} {Z' Z₁ G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G)
    (t : Z₁ ⟶ Z') (n : ℕ) (x : Ext.{w} Z F n) :
    (Ext.mk₀ t).comp (extMap.{w, w'} Φ a b n x) (zero_add n) =
      extMap.{w, w'} Φ (t ≫ a) b n x := by
  simp only [extMap_apply, Ext.mk₀_comp_mk₀_assoc]

private lemma comp_comp_mk0_eq_comp_comp_of_square {X₀ X₁ X₂ X₃ Y₂ Y₃ : B} {n : ℕ} (a : Ext.{w'} X₀ X₁ 0)
    (y : Ext.{w'} X₁ X₂ n) (e : Ext.{w'} X₂ X₃ 1) (t₃ : X₃ ⟶ Y₃) (t₂ : X₂ ⟶ Y₂)
    (f : Ext.{w'} Y₂ Y₃ 1)
    (h : e.comp (Ext.mk₀ t₃) (add_zero 1) = (Ext.mk₀ t₂).comp f (zero_add 1)) :
    a.comp ((y.comp e rfl).comp (Ext.mk₀ t₃) (add_zero _)) (zero_add _) =
      (a.comp (y.comp (Ext.mk₀ t₂) (add_zero n)) (zero_add n)).comp f rfl := by
  rw [Ext.comp_assoc_of_third_deg_zero, h, ← Ext.comp_assoc_of_second_deg_zero]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

lemma extMap_extClass {Z : A} {Z' : B} (a : Z' ⟶ Φ.obj Z) {S : ShortComplex A}
    {T : ShortComplex B} (hS : S.ShortExact) (hT : T.ShortExact) (φ : S.map Φ ⟶ T) (n : ℕ)
    (x : Ext.{w} Z S.X₃ n) :
    extMap.{w, w'} Φ a (F := S.X₁) φ.τ₁ (n + 1) (x.comp hS.extClass rfl) =
      (extMap.{w, w'} Φ a (F := S.X₃) φ.τ₃ n x).comp hT.extClass rfl := by
  erw [extMap_apply, extMap_apply]
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact comp_comp_mk0_eq_comp_comp_of_square _ _ _ _ _ _ ((hS.map_of_exact Φ).extClass_naturality hT φ)

end Abstract

section Site

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  (p : C ⥤ D) [p.IsContinuous J K]
  [(p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]

open SheafLES

instance additive_sheafPullback : (p.sheafPullback AddCommGrpCat.{v} J K).Additive :=
  have := (p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).isLeftAdjoint
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (p.sheafPullback AddCommGrpCat.{v} J K)
  Functor.additive_of_preservesBinaryBiproducts _

instance preservesFiniteColimits_sheafPullback :
    PreservesFiniteColimits (p.sheafPullback AddCommGrpCat.{v} J K) :=
  have := (p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).isLeftAdjoint
  inferInstance

instance additive_sheafPushforwardContinuous :
    (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).Additive where
  map_add := rfl

variable (J K) in

def freeToPullback {V : C} {W : D} (i : W ⟶ p.obj V) :
    (freeYoneda K).obj W ⟶ (p.sheafPullback AddCommGrpCat.{v} J K).obj ((freeYoneda J).obj V) :=
  (freeYonedaHomEquiv W _).symm
    (((p.sheafPullback AddCommGrpCat.{v} J K).obj ((freeYoneda J).obj V)).obj.map i.op
      (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app _).hom.app (op V)
        (tautSection V)))

lemma freeYonedaHomEquiv_freeToPullback_comp {V : C} {W : D} (i : W ⟶ p.obj V)
    {G : Sheaf K AddCommGrpCat.{v}}
    (b : (p.sheafPullback AddCommGrpCat.{v} J K).obj ((freeYoneda J).obj V) ⟶ G) :
    freeYonedaHomEquiv W G (freeToPullback J K p i ≫ b) =
      G.obj.map i.op (freeYonedaHomEquiv V _
        ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _ b)) := by
  rw [freeYonedaHomEquiv_comp, freeToPullback, Equiv.apply_symm_apply, Adjunction.homEquiv_unit,
    freeYonedaHomEquiv_apply]
  exact NatTrans.naturality_apply b.hom i.op _

lemma map_comp_freeToPullback {V : C} {W W' : D} (i : W ⟶ p.obj V) (k : W' ⟶ W) :
    (freeYoneda K).map k ≫ freeToPullback J K p i = freeToPullback J K p (k ≫ i) := by
  apply (freeYonedaHomEquiv W' _).injective
  rw [freeYonedaHomEquiv_map_comp, freeToPullback, freeToPullback, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, op_comp, Functor.map_comp]
  rfl

lemma freeToPullback_comp_map {V V' : C} {W : D} (i : W ⟶ p.obj V') (k : V' ⟶ V) :
    freeToPullback J K p i ≫ (p.sheafPullback AddCommGrpCat.{v} J K).map ((freeYoneda J).map k) =
      freeToPullback J K p (i ≫ p.map k) := by
  apply (freeYonedaHomEquiv W _).injective
  rw [freeYonedaHomEquiv_comp, freeToPullback, freeToPullback, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  have hu : ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app
        ((freeYoneda J).obj V)).hom.app (op V') (((freeYoneda J).map k).hom.app (op V') (tautSection V')) =
      ((p.sheafPullback AddCommGrpCat.{v} J K).map ((freeYoneda J).map k)).hom.app (op (p.obj V'))
        (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app
          ((freeYoneda J).obj V')).hom.app (op V') (tautSection V')) :=
    congrArg (fun f => f.hom.app (op V') (tautSection V'))
      ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.naturality ((freeYoneda J).map k))
  have ht : ((freeYoneda J).map k).hom.app (op V') (tautSection V') =
      ((freeYoneda J).obj V).obj.map k.op (tautSection V) := by
    rw [← freeYonedaHomEquiv_apply, ← Category.comp_id ((freeYoneda J).map k),
      freeYonedaHomEquiv_map_comp]
    rfl
  have e2 := NatTrans.naturality_apply
    ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app ((freeYoneda J).obj V)).hom k.op
    (tautSection V)
  have e3 := hu.symm.trans ((congrArg (fun z => ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).unit.app
    ((freeYoneda J).obj V)).hom.app (op V') z) ht).trans e2)
  refine (NatTrans.naturality_apply _ i.op _).trans ?_
  refine (congrArg (fun z => (((p.sheafPullback AddCommGrpCat.{v} J K).obj
    ((freeYoneda J).obj V)).obj.map i.op) z) e3).trans ?_
  rw [op_comp, Functor.map_comp]
  rfl

variable [PreservesFiniteLimits (p.sheafPullback AddCommGrpCat.{v} J K)]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]
  {F F' : Sheaf J AddCommGrpCat.{v}} {G G' : Sheaf K AddCommGrpCat.{v}}

def sitePull (φ : F ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G) (n : ℕ)
    {V : C} {W : D} (i : W ⟶ p.obj V) : Sheaf.H'.{w} F n V →+ Sheaf.H'.{w'} G n W :=
  extMap.{w, w'} (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i)
    (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ) n

lemma equivZero_sitePull (φ : F ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
    {V : C} {W : D} (i : W ⟶ p.obj V) (x : Sheaf.H'.{w} F 0 V) :
    equivZero G W (sitePull.{w, w'} p φ 0 i x) =
      G.obj.map i.op (φ.hom.app (op V) (equivZero F V x)) := by
  obtain ⟨g, rfl⟩ : ∃ g, Ext.mk₀ g = x := ⟨Ext.addEquiv₀ x, Ext.mk₀_addEquiv₀_apply x⟩
  unfold sitePull
  erw [extMap_mk₀]
  rw [equivZero_mk₀, equivZero_mk₀, freeYonedaHomEquiv_freeToPullback_comp,
    Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply, freeYonedaHomEquiv_comp]

lemma sitePull_map (φ : F' ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
    (s : F ⟶ F') (n : ℕ) {V : C} {W : D} (i : W ⟶ p.obj V) (x : Sheaf.H'.{w} F n V) :
    sitePull.{w, w'} p φ n i (map s n V x) = sitePull.{w, w'} p (s ≫ φ) n i x := by
  have h1 := extMap_comp_right (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i)
    (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ) s n x
  rw [← Adjunction.homEquiv_naturality_left_symm] at h1
  exact (congrArg (fun y => sitePull.{w, w'} p φ n i y) (map_apply s n V x)).trans h1

lemma map_sitePull (φ : F ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
    (t : G ⟶ G') (n : ℕ) {V : C} {W : D} (i : W ⟶ p.obj V) (x : Sheaf.H'.{w} F n V) :
    map t n W (sitePull.{w, w'} p φ n i x) = sitePull.{w, w'} p
      (φ ≫ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).map t) n i x := by
  have h1 := comp_extMap_right (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i)
    (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ) t n x
  rw [← Adjunction.homEquiv_naturality_right_symm] at h1
  exact (map_apply t n W _).trans h1

lemma sitePull_res (φ : F ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
    (n : ℕ) {V V' : C} {W : D} (i : W ⟶ p.obj V') (k : V' ⟶ V) (x : Sheaf.H'.{w} F n V) :
    sitePull.{w, w'} p φ n i (res F n k x) = sitePull.{w, w'} p φ n (i ≫ p.map k) x := by
  have h1 := extMap_comp_left (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i)
    (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ) ((freeYoneda J).map k) n x
  rw [freeToPullback_comp_map] at h1
  exact (congrArg (fun y => sitePull.{w, w'} p φ n i y) (res_apply n k x)).trans h1

lemma res_sitePull (φ : F ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
    (n : ℕ) {V : C} {W W' : D} (i : W ⟶ p.obj V) (k : W' ⟶ W) (x : Sheaf.H'.{w} F n V) :
    res G n k (sitePull.{w, w'} p φ n i x) = sitePull.{w, w'} p φ n (k ≫ i) x := by
  have h1 := comp_extMap_left (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i)
    (((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ) ((freeYoneda K).map k) n x
  rw [map_comp_freeToPullback] at h1
  exact (res_apply n k _).trans h1

lemma sitePull_δ {S : ShortComplex (Sheaf J AddCommGrpCat.{v})}
    {T : ShortComplex (Sheaf K AddCommGrpCat.{v})} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T.map (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K)) (n : ℕ)
    {V : C} {W : D} (i : W ⟶ p.obj V) (x : Sheaf.H'.{w} S.X₃ n V) :
    sitePull.{w, w'} p (G := T.X₁) φ.τ₁ (n + 1) i (δ hS n V x) =
      δ hT n W (sitePull.{w, w'} p (G := T.X₃) φ.τ₃ n i x) := by
  have h1 := extMap_extClass (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i) hS hT
    { τ₁ := ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ.τ₁
      τ₂ := ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ.τ₂
      τ₃ := ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ.τ₃
      comm₁₂ := by
        have h := congrArg ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm
          φ.comm₁₂
        exact (Adjunction.homEquiv_naturality_right_symm _ _ _).symm.trans
          (h.trans (Adjunction.homEquiv_naturality_left_symm _ _ _))
      comm₂₃ := by
        have h := congrArg ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm
          φ.comm₂₃
        exact (Adjunction.homEquiv_naturality_right_symm _ _ _).symm.trans
          (h.trans (Adjunction.homEquiv_naturality_left_symm _ _ _)) } n x
  exact (congrArg (fun y => sitePull.{w, w'} p (G := T.X₁) φ.τ₁ (n + 1) i y) (δ_apply hS n V x)).trans
    (h1.trans (δ_apply hT n W _).symm)

lemma sitePull_bijective_succ {S : ShortComplex (Sheaf J AddCommGrpCat.{v})}
    {T : ShortComplex (Sheaf K AddCommGrpCat.{v})} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T.map (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K)) (n : ℕ)
    {V : C} {W : D} (i : W ⟶ p.obj V)
    (h₂ : Function.Surjective (sitePull.{w, w'} p (G := T.X₂) φ.τ₂ n i))
    (h₃ : Function.Bijective (sitePull.{w, w'} p (G := T.X₃) φ.τ₃ n i))
    (hV : Subsingleton (Sheaf.H'.{w} S.X₂ (n + 1) V))
    (hW : Subsingleton (Sheaf.H'.{w'} T.X₂ (n + 1) W)) :
    Function.Bijective (sitePull.{w, w'} p (G := T.X₁) φ.τ₁ (n + 1) i) := by
  have hδS := δ_surjective_of_subsingleton hS n V hV
  have hδT := δ_surjective_of_subsingleton hT n W hW
  have hg : ∀ y, sitePull.{w, w'} p (G := T.X₃) φ.τ₃ n i (map S.g n V y) =
      map T.g n W (sitePull.{w, w'} p (G := T.X₂) φ.τ₂ n i y) := by
    intro y
    refine (sitePull_map p _ S.g n i y).trans ?_
    refine Eq.trans ?_ (map_sitePull p _ T.g n i y).symm
    exact congrArg (fun f => sitePull.{w, w'} p f n i y) φ.comm₂₃.symm
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨z, rfl⟩ := hδS a
    have ha' := (sitePull_δ p hS hT φ n i z).symm.trans ha
    obtain ⟨y, hy⟩ := ((exact₃ hT n W) _).1 ha'
    obtain ⟨y', rfl⟩ := h₂ y
    have hz : z = map S.g n V y' := h₃.1 ((hg y').trans hy).symm
    rw [hz, δ_map]
  · intro b
    obtain ⟨z, rfl⟩ := hδT b
    obtain ⟨z', rfl⟩ := h₃.2 z
    exact ⟨δ hS n V z', sitePull_δ p hS hT φ n i z'⟩

lemma sitePull_bijective_zero (φ : F ⟶ (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).obj G)
    {V : C} {W : D} (i : W ⟶ p.obj V)
    (h : Function.Bijective fun s : F.obj.obj (op V) ↦ G.obj.map i.op (φ.hom.app (op V) s)) :
    Function.Bijective (sitePull.{w, w'} p φ 0 i) := by
  have key : ⇑(equivZero G W) ∘ ⇑(sitePull.{w, w'} p φ 0 i) =
      (fun s : F.obj.obj (op V) ↦ G.obj.map i.op (φ.hom.app (op V) s)) ∘ ⇑(equivZero F V) :=
    funext (equivZero_sitePull p φ i)
  have hb := h.comp (equivZero F V).bijective
  rw [← key] at hb
  exact (EquivLike.comp_bijective _ (equivZero G W)).1 hb

end Site

end SheafPull

end GlobalTheory

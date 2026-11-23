import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite

namespace GlobalTheory.CompanionTheory.NerveCoh

structure Cx (R : Type) [CommRing R] where

  X : ℕ → ModuleCat.{0} R

  d : ∀ n, X n →ₗ[R] X (n + 1)
  d_d : ∀ n x, d (n + 1) (d n x) = 0

variable {R : Type} [CommRing R]

def Cx.Ex (A : Cx R) : ℕ → Prop
  | 0 => Function.Injective (A.d 0)
  | k + 1 => Function.Exact (A.d k) (A.d (k + 1))

structure Hm (A B : Cx R) where

  f : ∀ n, A.X n →ₗ[R] B.X n
  f_d : ∀ n x, f (n + 1) (A.d n x) = B.d n (f n x)

structure SES (A B C : Cx R) where

  i : Hm A B

  p : Hm B C
  inj : ∀ n, Function.Injective (i.f n)
  ex : ∀ n, Function.Exact (i.f n) (p.f n)
  surj : ∀ n, Function.Surjective (p.f n)

theorem Cx.ex_zero_iff {A : Cx R} : A.Ex 0 ↔ ∀ x, A.d 0 x = 0 → x = 0 :=
  injective_iff_map_eq_zero (A.d 0)

theorem Cx.ex_succ_iff {A : Cx R} {k : ℕ} : A.Ex (k + 1) ↔ ∀ x, A.d (k + 1) x = 0 → ∃ y, A.d k y = x :=
  ⟨fun h x hx ↦ (h x).1 hx, fun h x ↦ ⟨h x, fun ⟨y, e⟩ ↦ e ▸ A.d_d k y⟩⟩

theorem SES.ex_zero {A B C : Cx R} (S : SES A B C) (hB : B.Ex 0) : A.Ex 0 := by
  rw [Cx.ex_zero_iff] at hB ⊢
  intro x hx
  apply S.inj 0
  rw [map_zero]
  apply hB
  rw [← S.i.f_d, hx, map_zero]

theorem SES.ex_succ {A B C : Cx R} (S : SES A B C) (hB : ∀ k, B.Ex k) {k : ℕ} (hC : C.Ex k) :
    A.Ex (k + 1) := by
  rw [Cx.ex_succ_iff]
  intro x hx
  obtain ⟨y, hy⟩ := Cx.ex_succ_iff.1 (hB (k + 1)) (S.i.f (k + 1) x) (by
    rw [← S.i.f_d, hx, map_zero])
  have hpy : C.d k (S.p.f k y) = 0 := by
    rw [← S.p.f_d, hy]
    exact (S.ex (k + 1) _).2 ⟨x, rfl⟩
  suffices h : ∃ y' : B.X k, B.d k y' = B.d k y ∧ S.p.f k y' = 0 by
    obtain ⟨y', h1, h2⟩ := h
    obtain ⟨x', rfl⟩ := (S.ex k y').1 h2
    refine ⟨x', S.inj (k + 1) ?_⟩
    rw [S.i.f_d, h1, hy]
  cases k with
  | zero =>
    exact ⟨y, rfl, Cx.ex_zero_iff.1 hC _ hpy⟩
  | succ k =>
    obtain ⟨z, hz⟩ := Cx.ex_succ_iff.1 hC _ hpy
    obtain ⟨y', rfl⟩ := S.surj k z
    refine ⟨y - B.d k y', ?_, ?_⟩
    · rw [map_sub, B.d_d, sub_zero]
    · rw [map_sub, S.p.f_d, hz, sub_self]

theorem SES.ex_quot {A B C : Cx R} (S : SES A B C) (hA : ∀ k, A.Ex k) (hB : ∀ k, B.Ex k) (k : ℕ) :
    C.Ex k := by
  have key : ∀ (k : ℕ) (y : B.X k), C.d k (S.p.f k y) = 0 →
      ∃ x' : A.X k, B.d k (y - S.i.f k x') = 0 := by
    intro k y hy
    obtain ⟨x, hx⟩ := (S.ex (k + 1) (B.d k y)).1 (by rw [S.p.f_d, hy])
    obtain ⟨x', rfl⟩ := Cx.ex_succ_iff.1 (hA (k + 1)) x (S.inj (k + 2) (by
      rw [S.i.f_d, hx, B.d_d, map_zero]))
    refine ⟨x', ?_⟩
    rw [map_sub, ← S.i.f_d, hx, sub_self]
  cases k with
  | zero =>
    rw [Cx.ex_zero_iff]
    intro z hz
    obtain ⟨y, rfl⟩ := S.surj 0 z
    obtain ⟨x', hx'⟩ := key 0 y hz
    have := Cx.ex_zero_iff.1 (hB 0) _ hx'
    rw [sub_eq_zero] at this
    rw [this]
    exact (S.ex 0 _).2 ⟨x', rfl⟩
  | succ k =>
    rw [Cx.ex_succ_iff]
    intro z hz
    obtain ⟨y, rfl⟩ := S.surj (k + 1) z
    obtain ⟨x', hx'⟩ := key (k + 1) y hz
    obtain ⟨y', hy'⟩ := Cx.ex_succ_iff.1 (hB (k + 1)) _ hx'
    refine ⟨S.p.f k y', ?_⟩
    rw [← S.p.f_d, hy', map_sub, (S.ex (k + 1) _).2 ⟨x', rfl⟩, sub_zero]

def coneX {A B : Cx R} : ℕ → ModuleCat.{0} R
  | 0 => A.X 0
  | k + 1 => ModuleCat.of R (A.X (k + 1) × B.X k)

def cone {A B : Cx R} (f : Hm A B) : Cx R where
  X := coneX (A := A) (B := B)
  d
    | 0 => (LinearMap.prod (A.d 0) (f.f 0) : A.X 0 →ₗ[R] A.X 1 × B.X 0)
    | k + 1 => (LinearMap.prod (A.d (k + 1) ∘ₗ LinearMap.fst R _ _)
        (f.f (k + 1) ∘ₗ LinearMap.fst R _ _ - B.d k ∘ₗ LinearMap.snd R _ _) :
          A.X (k + 1) × B.X k →ₗ[R] A.X (k + 2) × B.X (k + 1))
  d_d
    | 0, x => Prod.ext (A.d_d 0 x) (sub_eq_zero.2 (f.f_d 0 x))
    | k + 1, x => Prod.ext (A.d_d (k + 1) _) (by
        show f.f (k + 2) (A.d (k + 1) x.1) - B.d (k + 1) (f.f (k + 1) x.1 - B.d k x.2) = 0
        rw [f.f_d, map_sub, B.d_d, sub_zero, sub_self])

theorem cone_ex_zero {A B : Cx R} (f : Hm A B) :
    (cone f).Ex 0 ↔ ∀ a, A.d 0 a = 0 → f.f 0 a = 0 → a = 0 := by
  rw [Cx.ex_zero_iff]
  exact ⟨fun h a h1 h2 ↦ h a (Prod.ext h1 h2), fun h a ha ↦ h a (congrArg Prod.fst ha) (congrArg Prod.snd ha)⟩

theorem cone_ex_one {A B : Cx R} (f : Hm A B) :
    (cone f).Ex 1 ↔ ∀ (a : A.X 1) (b : B.X 0), A.d 1 a = 0 → f.f 1 a = B.d 0 b →
      ∃ y, A.d 0 y = a ∧ f.f 0 y = b := by
  rw [Cx.ex_succ_iff]
  refine ⟨fun h a b h1 h2 ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨y, hy⟩ := h (a, b) (Prod.ext h1 (sub_eq_zero.2 h2))
    exact ⟨y, congrArg Prod.fst hy, congrArg Prod.snd hy⟩
  · obtain ⟨y, h1, h2⟩ := h x.1 x.2 (congrArg Prod.fst hx) (sub_eq_zero.1 (congrArg Prod.snd hx))
    exact ⟨y, Prod.ext h1 h2⟩

theorem cone_ex_succ {A B : Cx R} (f : Hm A B) (k : ℕ) :
    (cone f).Ex (k + 2) ↔ ∀ (a : A.X (k + 2)) (b : B.X (k + 1)), A.d (k + 2) a = 0 →
      f.f (k + 2) a = B.d (k + 1) b →
      ∃ (y : A.X (k + 1)) (z : B.X k), A.d (k + 1) y = a ∧ f.f (k + 1) y - B.d k z = b := by
  rw [Cx.ex_succ_iff]
  refine ⟨fun h a b h1 h2 ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨y, hy⟩ := h (a, b) (Prod.ext h1 (sub_eq_zero.2 h2))
    exact ⟨y.1, y.2, congrArg Prod.fst hy, congrArg Prod.snd hy⟩
  · obtain ⟨y, z, h1, h2⟩ := h x.1 x.2 (congrArg Prod.fst hx) (sub_eq_zero.1 (congrArg Prod.snd hx))
    exact ⟨(y, z), Prod.ext h1 h2⟩

theorem cone_ex_of_acyclic {A B : Cx R} (f : Hm A B) (hA : ∀ k, A.Ex (k + 1)) (hB : ∀ k, B.Ex (k + 1))
    (h0 : ∀ a, A.d 0 a = 0 → f.f 0 a = 0 → a = 0)
    (h1 : ∀ b, B.d 0 b = 0 → ∃ a, A.d 0 a = 0 ∧ f.f 0 a = b) (k : ℕ) : (cone f).Ex k := by
  match k with
  | 0 => exact (cone_ex_zero f).2 h0
  | 1 =>
    refine (cone_ex_one f).2 fun a b ha hb ↦ ?_
    obtain ⟨y, rfl⟩ := Cx.ex_succ_iff.1 (hA 0) a ha
    obtain ⟨y', h2, h3⟩ := h1 (b - f.f 0 y) (by rw [map_sub, ← hb, f.f_d, sub_self])
    exact ⟨y + y', by rw [map_add, h2, add_zero], by rw [map_add, h3, add_sub_cancel]⟩
  | k + 2 =>
    refine (cone_ex_succ f k).2 fun a b ha hb ↦ ?_
    obtain ⟨y, rfl⟩ := Cx.ex_succ_iff.1 (hA (k + 1)) a ha
    obtain ⟨z, hz⟩ := Cx.ex_succ_iff.1 (hB k) (f.f (k + 1) y - b) (by
      rw [map_sub, ← hb, f.f_d, sub_self])
    exact ⟨y, z, rfl, by rw [hz, sub_sub_cancel]⟩

def SES.cone {A A' A'' B B' B'' : Cx R} (S : SES A A' A'') (T : SES B B' B'') (f : Hm A B) (f' : Hm A' B')
    (f'' : Hm A'' B'') (h1 : ∀ n x, f'.f n (S.i.f n x) = T.i.f n (f.f n x))
    (h2 : ∀ n x, f''.f n (S.p.f n x) = T.p.f n (f'.f n x)) :
    SES (GlobalTheory.CompanionTheory.NerveCoh.cone f) (GlobalTheory.CompanionTheory.NerveCoh.cone f') (GlobalTheory.CompanionTheory.NerveCoh.cone f'') where
  i :=
    { f
        | 0 => S.i.f 0
        | k + 1 => (LinearMap.prodMap (S.i.f (k + 1)) (T.i.f k) : A.X (k + 1) × B.X k →ₗ[R] A'.X (k + 1) × B'.X k)
      f_d
        | 0, x => Prod.ext (S.i.f_d 0 x) (h1 0 x).symm
        | k + 1, x => Prod.ext (S.i.f_d (k + 1) _) (by
            show T.i.f (k + 1) (f.f (k + 1) x.1 - B.d k x.2) =
              f'.f (k + 1) (S.i.f (k + 1) x.1) - B'.d k (T.i.f k x.2)
            rw [map_sub, h1, T.i.f_d]) }
  p :=
    { f
        | 0 => S.p.f 0
        | k + 1 => (LinearMap.prodMap (S.p.f (k + 1)) (T.p.f k) : A'.X (k + 1) × B'.X k →ₗ[R] A''.X (k + 1) × B''.X k)
      f_d
        | 0, x => Prod.ext (S.p.f_d 0 x) (h2 0 x).symm
        | k + 1, x => Prod.ext (S.p.f_d (k + 1) _) (by
            show T.p.f (k + 1) (f'.f (k + 1) x.1 - B'.d k x.2) =
              f''.f (k + 1) (S.p.f (k + 1) x.1) - B''.d k (T.p.f k x.2)
            rw [map_sub, h2, T.p.f_d]) }
  inj
    | 0 => S.inj 0
    | k + 1 => Function.Injective.prodMap (S.inj (k + 1)) (T.inj k)
  ex
    | 0 => S.ex 0
    | k + 1 => fun x ↦ by
        constructor
        · intro hx
          obtain ⟨a, ha⟩ := (S.ex (k + 1) x.1).1 (congrArg Prod.fst hx)
          obtain ⟨b, hb⟩ := (T.ex k x.2).1 (congrArg Prod.snd hx)
          exact ⟨(a, b), Prod.ext ha hb⟩
        · rintro ⟨y, rfl⟩
          exact Prod.ext ((S.ex (k + 1) _).2 ⟨y.1, rfl⟩) ((T.ex k _).2 ⟨y.2, rfl⟩)
  surj
    | 0 => S.surj 0
    | k + 1 => Function.Surjective.prodMap (S.surj (k + 1)) (T.surj k)

section Cochains

variable {C : Type} [Category.{0} C]

abbrev MCn (F : C ⥤ ModuleCat.{0} R) (n : ℕ) : Type := ∀ c : Fin (n + 1) ⥤ C, F.obj (c.obj (Fin.last n))

def gp (F : C ⥤ ModuleCat.{0} R) {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) : MCn F m →ₗ[R] MCn F n :=
  LinearMap.pi fun c ↦ (F.map (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).hom ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (m + 1) ⥤ C ↦ (F.obj (c.obj (Fin.last m)) : Type))
      (θ.monotone.functor ⋙ c)

theorem gp_apply (F : C ⥤ ModuleCat.{0} R) {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : MCn F m)
    (c : Fin (n + 1) ⥤ C) : gp F θ f c =
      F.map (c.map (homOfLE (Fin.le_last (θ (Fin.last m))))) (f (θ.monotone.functor ⋙ c)) := rfl

theorem gp_id (F : C ⥤ ModuleCat.{0} R) (n : ℕ) (f : MCn F n) : gp F OrderHom.id f = f := by
  funext c
  show (F.map (c.map (𝟙 (Fin.last n)))).hom (f c) = f c
  simp

theorem gp_comp (F : C ⥤ ModuleCat.{0} R) {l m n : ℕ} (θ : Fin (l + 1) →o Fin (m + 1))
    (η : Fin (m + 1) →o Fin (n + 1)) (f : MCn F l) : gp F (η.comp θ) f = gp F η (gp F θ f) := by
  funext c
  have A : η (θ (Fin.last l)) ≤ Fin.last n := Fin.le_last _
  have B : η (θ (Fin.last l)) ≤ η (Fin.last m) := η.monotone (Fin.le_last _)
  have D : η (Fin.last m) ≤ Fin.last n := Fin.le_last _
  have key : c.map (homOfLE A) = c.map (homOfLE B) ≫ c.map (homOfLE D) := by
    rw [← c.map_comp]; rfl
  show (F.map (c.map (homOfLE A))).hom _ = (F.map (c.map (homOfLE D))).hom ((F.map (c.map (homOfLE B))).hom _)
  rw [key, F.map_comp]
  rfl

def cosim (F : C ⥤ ModuleCat.{0} R) : CosimplicialObject (ModuleCat.{0} R) where
  obj Δ := ModuleCat.of R (MCn F Δ.len)
  map θ := ModuleCat.ofHom (gp F θ.toOrderHom)
  map_id Δ := ModuleCat.hom_ext (LinearMap.ext fun f ↦ gp_id F _ f)
  map_comp θ η := ModuleCat.hom_ext (LinearMap.ext fun f ↦ gp_comp F _ _ f)

def mdn (F : C ⥤ ModuleCat.{0} R) (n : ℕ) : MCn F n →ₗ[R] MCn F (n + 1) :=
  ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • gp F (Fin.succAboveOrderEmb i).toOrderHom

theorem objD_hom (F : C ⥤ ModuleCat.{0} R) (n : ℕ) (f : MCn F n) :
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosim F) n).hom f = mdn F n f := by
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, mdn, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_zsmul, LinearMap.smul_apply]
  refine (LinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  refine (LinearMap.smul_apply _ _ _).trans ?_
  rw [← Int.cast_smul_eq_zsmul R]
  push_cast
  rfl

theorem mdn_mdn (F : C ⥤ ModuleCat.{0} R) (n : ℕ) (f : MCn F n) : mdn F (n + 1) (mdn F n f) = 0 := by
  have h := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (cosim F) n
  have h2 := congrArg (fun φ ↦ φ.hom f) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [← objD_hom, ← objD_hom]
  exact h2

end Cochains

section Maps

variable {C C' D : Type} [Category.{0} C] [Category.{0} C'] [Category.{0} D]

def cn (F : C ⥤ ModuleCat.{0} R) : Cx R where
  X n := ModuleCat.of R (MCn F n)
  d n := mdn F n
  d_d n f := mdn_mdn F n f

def pb (Φ : C' ⥤ C) {F : C ⥤ ModuleCat.{0} R} {G : C' ⥤ ModuleCat.{0} R} (α : Φ ⋙ F ⟶ G) (n : ℕ) :
    MCn F n →ₗ[R] MCn G n :=
  LinearMap.pi fun c ↦ (α.app (c.obj (Fin.last n))).hom ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (n + 1) ⥤ C ↦ (F.obj (c.obj (Fin.last n)) : Type)) (c ⋙ Φ)

theorem pb_apply (Φ : C' ⥤ C) {F : C ⥤ ModuleCat.{0} R} {G : C' ⥤ ModuleCat.{0} R} (α : Φ ⋙ F ⟶ G) (n : ℕ)
    (f : MCn F n) (c : Fin (n + 1) ⥤ C') : pb Φ α n f c = (α.app (c.obj (Fin.last n))).hom (f (c ⋙ Φ)) := rfl

theorem pb_gp (Φ : C' ⥤ C) {F : C ⥤ ModuleCat.{0} R} {G : C' ⥤ ModuleCat.{0} R} (α : Φ ⋙ F ⟶ G) {m n : ℕ}
    (θ : Fin (m + 1) →o Fin (n + 1)) (f : MCn F m) : pb Φ α n (gp F θ f) = gp G θ (pb Φ α m f) := by
  funext c
  have h := α.naturality (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))
  have h2 := congrArg (fun φ ↦ φ.hom (f (θ.monotone.functor ⋙ c ⋙ Φ))) h
  exact h2

theorem pb_mdn (Φ : C' ⥤ C) {F : C ⥤ ModuleCat.{0} R} {G : C' ⥤ ModuleCat.{0} R} (α : Φ ⋙ F ⟶ G) (n : ℕ)
    (f : MCn F n) : pb Φ α (n + 1) (mdn F n f) = mdn G n (pb Φ α n f) := by
  simp only [mdn, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, pb_gp]

def pbH (Φ : C' ⥤ C) {F : C ⥤ ModuleCat.{0} R} {G : C' ⥤ ModuleCat.{0} R} (α : Φ ⋙ F ⟶ G) : Hm (cn F) (cn G) where
  f n := pb Φ α n
  f_d n f := pb_mdn Φ α n f

abbrev post {F G : C ⥤ ModuleCat.{0} R} (α : F ⟶ G) : Hm (cn F) (cn G) := pbH (𝟭 C) (F := F) (G := G) α

structure PtSES {F F' F'' : C ⥤ ModuleCat.{0} R} (φ : F ⟶ F') (ψ : F' ⟶ F'') : Prop where
  inj : ∀ x, Function.Injective (φ.app x).hom
  ex : ∀ x, Function.Exact (φ.app x).hom (ψ.app x).hom
  surj : ∀ x, Function.Surjective (ψ.app x).hom

def cnSES {F F' F'' : C ⥤ ModuleCat.{0} R} {φ : F ⟶ F'} {ψ : F' ⟶ F''} (h : PtSES φ ψ) :
    SES (cn F) (cn F') (cn F'') where
  i := post φ
  p := post ψ
  inj n f g e := funext fun c ↦ h.inj _ (congrFun e c)
  ex n f := by
    constructor
    · intro hf
      have : ∀ c, ∃ y, (φ.app (c.obj (Fin.last n))).hom y = f c := fun c ↦
        (h.ex _ (f c)).1 (congrFun hf c)
      choose y hy using this
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      exact funext fun c ↦ (h.ex _ _).2 ⟨y (c ⋙ 𝟭 C), rfl⟩
  surj n f := by
    have : ∀ c, ∃ y, (ψ.app (c.obj (Fin.last n))).hom y = f c := fun c ↦ h.surj _ (f c)
    choose y hy using this
    exact ⟨y, funext hy⟩

def coker {F F' : C ⥤ ModuleCat.{0} R} (φ : F ⟶ F') : C ⥤ ModuleCat.{0} R where
  obj x := ModuleCat.of R (F'.obj x ⧸ LinearMap.range (φ.app x).hom)
  map {x y} g := ModuleCat.ofHom (Submodule.mapQ _ _ (F'.map g).hom (by
    rintro _ ⟨v, rfl⟩
    refine ⟨(F.map g).hom v, ?_⟩
    exact congrArg (fun t ↦ t.hom v) (φ.naturality g)))
  map_id x := ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun v ↦ by simp))
  map_comp g g' := ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun v ↦ by simp))

def cokerπ {F F' : C ⥤ ModuleCat.{0} R} (φ : F ⟶ F') : F' ⟶ coker φ where
  app x := ModuleCat.ofHom (Submodule.mkQ _)
  naturality x y g := ModuleCat.hom_ext (LinearMap.ext fun v ↦ rfl)

theorem ptSES_coker {F F' : C ⥤ ModuleCat.{0} R} {φ : F ⟶ F'} (h : ∀ x, Function.Injective (φ.app x).hom) :
    PtSES φ (cokerπ φ) where
  inj := h
  ex x v := by
    show Submodule.mkQ _ v = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl
  surj x := Submodule.mkQ_surjective _

end Maps

section Coind

variable {E : Type} [Category.{0} E]

abbrev fc {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ E) : Fin (n + 1) ⥤ E :=
  (Fin.succAboveOrderEmb i).toOrderHom.monotone.functor ⋙ c

theorem mdn_apply (H : E ⥤ ModuleCat.{0} R) (n : ℕ) (f : MCn H n) (c : Fin (n + 2) ⥤ E) :
    mdn H n f c = ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) •
      (H.map (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n)))))).hom (f (fc i c)) := by
  simp only [mdn, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply]
  rfl

abbrev pt (y : E) : Fin 1 ⥤ E := (Functor.const _).obj y

variable [Quiver.IsThin E]

theorem snoc_nonempty {n : ℕ} (c : Fin (n + 1) ⥤ E) (y : E) (f : c.obj (Fin.last n) ⟶ y) {i j : Fin (n + 2)}
    (h : i ≤ j) : Nonempty ((Fin.snoc (α := fun _ ↦ E) c.obj y i : E) ⟶ (Fin.snoc (α := fun _ ↦ E) c.obj y j : E)) := by
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last => exact ⟨𝟙 _⟩
    | cast i =>
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact ⟨c.map (homOfLE (Fin.le_last i)) ≫ f⟩
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact absurd h (not_le.2 (Fin.castSucc_lt_last j))
    | cast i =>
      simp only [Fin.snoc_castSucc]
      exact ⟨c.map (homOfLE (Fin.castSucc_le_castSucc_iff.1 h))⟩

def snoc {n : ℕ} (c : Fin (n + 1) ⥤ E) (y : E) (f : c.obj (Fin.last n) ⟶ y) : Fin (n + 2) ⥤ E where
  obj := Fin.snoc (α := fun _ ↦ E) c.obj y
  map h := Classical.choice (snoc_nonempty c y f (leOfHom h))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

theorem snoc_obj_last {n : ℕ} (c : Fin (n + 1) ⥤ E) (y : E) (f : c.obj (Fin.last n) ⟶ y) :
    (snoc c y f).obj (Fin.last _) = y := by
  simp [snoc]

theorem snoc_obj_castSucc {n : ℕ} (c : Fin (n + 1) ⥤ E) (y : E) (f : c.obj (Fin.last n) ⟶ y) (i : Fin (n + 1)) :
    (snoc c y f).obj i.castSucc = c.obj i := by
  simp [snoc]

def lastH {n : ℕ} (c : Fin (n + 1) ⥤ E) (y : E) (f : c.obj (Fin.last n) ⟶ y) :
    (snoc c y f).obj (Fin.last _) ⟶ y := eqToHom (snoc_obj_last c y f)

theorem chain_ext {n : ℕ} {c c' : Fin n ⥤ E} (h : ∀ i, c.obj i = c'.obj i) : c = c' :=
  CategoryTheory.Functor.ext h fun _ _ _ ↦ Subsingleton.elim _ _

theorem fc_last_snoc {n : ℕ} (c : Fin (n + 1) ⥤ E) (y : E) (f : c.obj (Fin.last n) ⟶ y) :
    fc (Fin.last _) (snoc c y f) = c := chain_ext fun i ↦ by
  show (snoc c y f).obj ((Fin.last _).succAbove i) = _
  rw [Fin.succAbove_last, snoc_obj_castSucc]

theorem sa_last {n : ℕ} (i : Fin (n + 2)) : i.castSucc.succAbove (Fin.last n.succ) = Fin.last (n + 2) := by
  rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.2 (Fin.le_last i)), Fin.succ_last]

theorem sa_cast {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1)) :
    i.castSucc.succAbove k.castSucc = (i.succAbove k).castSucc := by
  apply Fin.ext
  simp only [Fin.succAbove, Fin.lt_def]
  split_ifs <;> simp_all <;> omega

theorem fc_castSucc_snoc {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ E) (y : E) (f : c.obj (Fin.last _) ⟶ y)
    (g : (fc i c).obj (Fin.last n) ⟶ y) : fc i.castSucc (snoc c y f) = snoc (fc i c) y g := chain_ext fun k ↦ by
  show (snoc c y f).obj (i.castSucc.succAbove k) = _
  induction k using Fin.lastCases with
  | last =>
    rw [snoc_obj_last, sa_last, snoc_obj_last]
  | cast k =>
    rw [snoc_obj_castSucc, sa_cast, snoc_obj_castSucc]
    rfl

theorem fc_zero_snoc (c : Fin 1 ⥤ E) (y : E) (f : c.obj (Fin.last 0) ⟶ y) : fc 0 (snoc c y f) = pt y :=
  chain_ext fun k ↦ by
    show (snoc c y f).obj (Fin.succAbove 0 k) = y
    have : Fin.succAbove 0 k = Fin.last 1 := by
      rw [Fin.fin_one_eq_zero k]; rfl
    rw [this, snoc_obj_last]

structure CoD (H : E ⥤ ModuleCat.{0} R) (B : E → ModuleCat.{0} R) where

  ev : ∀ {x y : E}, (x ⟶ y) → (H.obj x →ₗ[R] B y)
  ev_map : ∀ {x x' y : E} (g : x ⟶ x') (f : x' ⟶ y) (v : H.obj x), ev f ((H.map g).hom v) = ev (g ≫ f) v
  ext : ∀ {x : E} (v : H.obj x), (∀ (y : E) (f : x ⟶ y), ev f v = 0) → v = 0
  ex : ∀ {x : E} (b : ∀ y : E, (x ⟶ y) → B y), ∃ v : H.obj x, ∀ (y : E) (f : x ⟶ y), ev f v = b y f

variable {H : E ⥤ ModuleCat.{0} R} {B : E → ModuleCat.{0} R}

theorem CoD.ev_congr (A : CoD H B) {n : ℕ} (φ : MCn H n) {c c' : Fin (n + 1) ⥤ E} (h : c = c') {y : E}
    (g : c.obj (Fin.last n) ⟶ y) (g' : c'.obj (Fin.last n) ⟶ y) : A.ev g (φ c) = A.ev g' (φ c') := by
  subst h
  rw [Subsingleton.elim g g']

theorem CoD.ev_mdn (A : CoD H B) {n : ℕ} (f : MCn H n) (c : Fin (n + 2) ⥤ E) {y : E}
    (g : c.obj (Fin.last _) ⟶ y) : A.ev g (mdn H n f c) = ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) •
      A.ev (c.map (homOfLE (Fin.le_last (i.succAbove (Fin.last n)))) ≫ g) (f (fc i c)) := by
  rw [mdn_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul]
  congr 1
  exact A.ev_map _ _ _

theorem CoD.key (A : CoD H B) (a : MCn H 0) (ha : mdn H 0 a = 0) (c : Fin 1 ⥤ E) {y : E}
    (g : c.obj (Fin.last 0) ⟶ y) : A.ev g (a c) = A.ev (𝟙 y) (a (pt y)) := by
  have h := A.ev_mdn a (snoc c y g) (lastH c y g)
  rw [ha, Fin.sum_univ_two] at h
  have e1 : ∀ m : (fc 0 (snoc c y g)).obj (Fin.last 0) ⟶ y, A.ev m (a (fc 0 (snoc c y g))) = A.ev (𝟙 y) (a (pt y)) :=
    fun m ↦ A.ev_congr a (fc_zero_snoc c y g) m _
  have e2 : ∀ m : (fc 1 (snoc c y g)).obj (Fin.last 0) ⟶ y, A.ev m (a (fc 1 (snoc c y g))) = A.ev g (a c) :=
    fun m ↦ A.ev_congr a (fc_last_snoc c y g) m g
  have h' : (0 : B y) = ((-1 : R) ^ ((0 : Fin 2) : ℕ)) • A.ev (𝟙 y) (a (pt y)) +
      ((-1 : R) ^ ((1 : Fin 2) : ℕ)) • A.ev g (a c) :=
    (map_zero _).symm.trans (h.trans (congrArg₂ (· + ·) (congrArg _ (e1 _)) (congrArg _ (e2 _))))
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h'
  exact (sub_eq_zero.1 ((sub_eq_add_neg _ _).trans h'.symm)).symm

theorem CoD.zero_ext (A : CoD H B) (a : MCn H 0) (ha : mdn H 0 a = 0)
    (h0 : ∀ y, A.ev (𝟙 y) (a (pt y)) = 0) : a = 0 := by
  funext c
  refine A.ext _ fun y f ↦ ?_
  rw [A.key a ha c f, h0]

theorem CoD.uniq (A : CoD H B) (p q : MCn H 0) (hp : mdn H 0 p = 0) (hq : mdn H 0 q = 0)
    (h : ∀ y, A.ev (𝟙 y) (p (pt y)) = A.ev (𝟙 y) (q (pt y))) : p = q := by
  rw [← sub_eq_zero]
  refine A.zero_ext _ (by rw [map_sub, hp, hq, sub_self]) fun y ↦ ?_
  rw [Pi.sub_apply, map_sub, h, sub_self]

theorem CoD.zero_ex (A : CoD H B) (b : ∀ y, B y) :
    ∃ a : MCn H 0, mdn H 0 a = 0 ∧ ∀ y, A.ev (𝟙 y) (a (pt y)) = b y := by
  have : ∀ c : Fin 1 ⥤ E, ∃ v : H.obj (c.obj (Fin.last 0)), ∀ (y : E) (f : c.obj (Fin.last 0) ⟶ y), A.ev f v = b y :=
    fun c ↦ A.ex fun y _ ↦ b y
  choose a ha using this
  refine ⟨a, ?_, fun y ↦ ha (pt y) y (𝟙 y)⟩
  funext c
  refine A.ext _ fun y f ↦ ?_
  rw [A.ev_mdn, Fin.sum_univ_two]
  have e : (0 : B y) = ((-1 : R) ^ ((0 : Fin 2) : ℕ)) • b y + ((-1 : R) ^ ((1 : Fin 2) : ℕ)) • b y := by simp
  exact (congrArg₂ (· + ·) (congrArg _ (ha (fc 0 c) y _)) (congrArg _ (ha (fc 1 c) y _))).trans e.symm

theorem CoD.exact (A : CoD H B) (n : ℕ) (φ : MCn H (n + 1)) (hφ : mdn H (n + 1) φ = 0) :
    ∃ ψ, mdn H n ψ = φ := by
  have : ∀ c : Fin (n + 1) ⥤ E, ∃ v : H.obj (c.obj (Fin.last n)), ∀ (y : E) (f : c.obj (Fin.last n) ⟶ y),
      A.ev f v = A.ev (lastH c y f) (φ (snoc c y f)) := fun c ↦ A.ex _
  choose ψ hψ using this
  have main : ∀ (c : Fin (n + 2) ⥤ E) (y : E) (f : c.obj (Fin.last _) ⟶ y),
      A.ev f (mdn H n ψ c) + ((-1 : R) ^ (n + 2)) • A.ev f (φ c) = 0 := by
    intro c y f
    have h := A.ev_mdn φ (snoc c y f) (lastH c y f)
    rw [hφ, Fin.sum_univ_castSucc] at h
    have h0 := (map_zero (A.ev (lastH c y f))).symm.trans h
    rw [A.ev_mdn]
    refine Eq.trans ?_ h0.symm
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ ↦ ?_) ?_
    · rw [Fin.val_castSucc]
      refine congrArg _ ((hψ (fc i c) y _).trans ?_)
      exact (A.ev_congr φ (fc_castSucc_snoc i c y f _) _ _).symm
    · rw [Fin.val_last]
      exact congrArg _ (A.ev_congr φ (fc_last_snoc c y f) _ _).symm
  refine ⟨(-((-1 : R) ^ (n + 2))) • ψ, ?_⟩
  rw [map_smul]
  funext c
  rw [← sub_eq_zero]
  refine A.ext _ fun y f ↦ ?_
  have hs : ((-1 : R) ^ (n + 2)) * ((-1 : R) ^ (n + 2)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  have := main c y f
  rw [add_eq_zero_iff_eq_neg] at this
  simp only [Pi.sub_apply, Pi.smul_apply, map_sub, map_neg, map_smul, this, smul_neg, neg_smul, neg_neg, smul_smul, hs,
    one_smul, sub_self]

end Coind

section Triple

theorem alt2 {M : Type} [AddCommGroup M] [Module R M] (z : M) :
    ((-1 : R) ^ ((0 : Fin 2) : ℕ)) • z + ((-1 : R) ^ ((1 : Fin 2) : ℕ)) • z = 0 := by
  simp

def coind {E : Type} [Category.{0} E] (B : E → ModuleCat.{0} R) : E ⥤ ModuleCat.{0} R where
  obj x := ModuleCat.of R (∀ p : (Σ y : E, (x ⟶ y)), B p.1)
  map {x x'} g := ModuleCat.ofHom (LinearMap.pi fun p : (Σ y : E, (x' ⟶ y)) ↦
    LinearMap.proj (R := R) (φ := fun p : (Σ y : E, (x ⟶ y)) ↦ (B p.1 : Type)) ⟨p.1, g ≫ p.2⟩)
  map_id x := ModuleCat.hom_ext (LinearMap.ext fun v ↦ funext fun p ↦ by
    show v ⟨p.1, 𝟙 _ ≫ p.2⟩ = v p
    rw [Category.id_comp])
  map_comp g g' := ModuleCat.hom_ext (LinearMap.ext fun v ↦ funext fun p ↦ by
    show v ⟨p.1, (g ≫ g') ≫ p.2⟩ = v ⟨p.1, g ≫ g' ≫ p.2⟩
    rw [Category.assoc])

def coindD {E : Type} [Category.{0} E] (B : E → ModuleCat.{0} R) : CoD (coind B) B where
  ev {x y} f := LinearMap.proj (R := R) (φ := fun p : (Σ y : E, (x ⟶ y)) ↦ (B p.1 : Type)) ⟨y, f⟩
  ev_map _ _ _ := rfl
  ext v h := funext fun p ↦ h p.1 p.2
  ex b := ⟨fun p ↦ b p.1 p.2, fun _ _ ↦ rfl⟩

def coindη {E : Type} [Category.{0} E] (G : E ⥤ ModuleCat.{0} R) : G ⟶ coind G.obj where
  app x := ModuleCat.ofHom (LinearMap.pi fun p : (Σ y : E, (x ⟶ y)) ↦ (G.map p.2).hom)
  naturality x x' g := ModuleCat.hom_ext (LinearMap.ext fun v ↦ funext fun p ↦ by
    show (G.map p.2).hom ((G.map g).hom v) = (G.map (g ≫ p.2)).hom v
    simp)

theorem coindη_inj {E : Type} [Category.{0} E] (G : E ⥤ ModuleCat.{0} R) (x : E) :
    Function.Injective ((coindη G).app x).hom := fun v w h ↦ by
  have h2 : (G.map (𝟙 x)).hom v = (G.map (𝟙 x)).hom w := congrFun h ⟨x, 𝟙 x⟩
  simpa using h2

variable (R) in

structure Tr (C D : Type) [Category.{0} C] [Category.{0} D] where

  F : C ⥤ ModuleCat.{0} R

  G : C × D ⥤ ModuleCat.{0} R

  α : CategoryTheory.Prod.fst C D ⋙ F ⟶ G

variable {C D : Type} [Category.{0} C] [Category.{0} D]

namespace Tr

variable (τ : Tr R C D)

abbrev pull : Hm (cn τ.F) (cn τ.G) := pbH (CategoryTheory.Prod.fst C D) τ.α

abbrev fibG (T : C) : D ⥤ ModuleCat.{0} R := CategoryTheory.Prod.sectR T D ⋙ τ.G

def fib (T : C) : τ.F.obj T →ₗ[R] MCn (τ.fibG T) 0 :=
  LinearMap.pi fun c ↦ (τ.α.app (T, c.obj (Fin.last 0))).hom

theorem fib_nat (T : C) {U U' : D} (g : U ⟶ U') (x : τ.F.obj T) :
    ((τ.fibG T).map g).hom ((τ.α.app (T, U)).hom x) = (τ.α.app (T, U')).hom x := by
  have h : (τ.α.app (T, U')).hom ((τ.F.map (𝟙 T)).hom x) = ((τ.fibG T).map g).hom ((τ.α.app (T, U)).hom x) :=
    congrArg (fun t ↦ t.hom x) (τ.α.naturality ((CategoryTheory.Prod.sectR T D).map g))
  rw [← h, τ.F.map_id]
  rfl

theorem fib_d (T : C) (x : τ.F.obj T) : mdn (τ.fibG T) 0 (τ.fib T x) = 0 := by
  funext c
  rw [mdn_apply, Fin.sum_univ_two]
  exact (congrArg₂ (· + ·) (congrArg _ (τ.fib_nat T _ x)) (congrArg _ (τ.fib_nat T _ x))).trans (alt2 _)

def augX (T : C) : ℕ → ModuleCat.{0} R
  | 0 => τ.F.obj T
  | k + 1 => ModuleCat.of R (MCn (τ.fibG T) k)

def aug (T : C) : Cx R where
  X := τ.augX T
  d
    | 0 => τ.fib T
    | k + 1 => mdn (τ.fibG T) k
  d_d
    | 0, x => τ.fib_d T x
    | k + 1, x => mdn_mdn _ k x

abbrev J : C ⥤ ModuleCat.{0} R := coind fun T ↦ ModuleCat.of R (∀ U : D, τ.G.obj (T, U))

abbrev I : C × D ⥤ ModuleCat.{0} R := coind τ.G.obj

@[reducible] def up : Tr R C D where
  F := τ.J
  G := τ.I
  α :=
    { app := fun x ↦ ModuleCat.ofHom (LinearMap.pi fun p : (Σ y : C × D, (x ⟶ y)) ↦
        LinearMap.proj (R := R) (φ := fun U : D ↦ (τ.G.obj (p.1.1, U) : Type)) p.1.2 ∘ₗ
        LinearMap.proj (R := R) (φ := fun q : (Σ T' : C, (x.1 ⟶ T')) ↦ ((ModuleCat.of R (∀ U : D, τ.G.obj (q.1, U))) : Type))
          ⟨p.1.1, p.2.1⟩)
      naturality := fun x x' φ ↦ ModuleCat.hom_ext (LinearMap.ext fun v ↦ rfl) }

def ηF : τ.F ⟶ τ.J where
  app T := ModuleCat.ofHom (LinearMap.pi fun p : (Σ T' : C, (T ⟶ T')) ↦ LinearMap.pi fun U : D ↦
    (τ.α.app (p.1, U)).hom ∘ₗ (τ.F.map p.2).hom)
  naturality T T' g := ModuleCat.hom_ext (LinearMap.ext fun v ↦ funext fun p ↦ funext fun U ↦ by
    show (τ.α.app (p.1, U)).hom ((τ.F.map p.2).hom ((τ.F.map g).hom v)) = (τ.α.app (p.1, U)).hom ((τ.F.map (g ≫ p.2)).hom v)
    simp)

abbrev ηG : τ.G ⟶ τ.I := coindη τ.G

theorem comm (x : C × D) (v : τ.F.obj x.1) :
    (τ.up.α.app x).hom ((τ.ηF.app x.1).hom v) = (τ.ηG.app x).hom ((τ.α.app x).hom v) := by
  funext p
  have h := congrArg (fun t ↦ t.hom v) (τ.α.naturality p.2)
  exact h

def quo : Tr R C D where
  F := coker τ.ηF
  G := coker τ.ηG
  α :=
    { app := fun x ↦ ModuleCat.ofHom (Submodule.mapQ _ _ (τ.up.α.app x).hom (by
        rintro _ ⟨v, rfl⟩
        exact ⟨(τ.α.app x).hom v, (τ.comm x v).symm⟩))
      naturality := fun x x' φ ↦ ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun v ↦ by
        have h := congrArg (fun t ↦ t.hom v) (τ.up.α.naturality φ)
        exact congrArg (Submodule.Quotient.mk (p := LinearMap.range (τ.ηG.app x').hom)) h)) }

end Tr

end Triple

section Main

variable {C D : Type} [Category.{0} C] [Category.{0} D]

theorem CoD.ev_inj {E : Type} [Category.{0} E] {H : E ⥤ ModuleCat.{0} R} {B : E → ModuleCat.{0} R} (A : CoD H B)
    {x : E} {v w : H.obj x} (h : ∀ (y : E) (f : x ⟶ y), A.ev f v = A.ev f w) : v = w := by
  rw [← sub_eq_zero]
  exact A.ext _ fun y f ↦ by rw [map_sub, h, sub_self]

instance thinProd [Quiver.IsThin C] [Quiver.IsThin D] : Quiver.IsThin (C × D) := fun a b ↦
  ⟨fun f g ↦ by
    have h1 : f.1 = g.1 := Subsingleton.elim _ _
    have h2 : f.2 = g.2 := Subsingleton.elim _ _
    exact Prod.ext h1 h2⟩

namespace Tr

variable (τ : Tr R C D)

def fibD [Quiver.IsThin C] [Quiver.IsThin D] (T : C) :
    CoD (τ.up.fibG T) (fun U' ↦ ModuleCat.of R (∀ p : (Σ T' : C, (T ⟶ T')), τ.G.obj (p.1, U'))) where
  ev {U U'} g := LinearMap.pi fun p : (Σ T' : C, (T ⟶ T')) ↦
    LinearMap.proj (R := R) (φ := fun q : (Σ y : C × D, ((T, U) ⟶ y)) ↦ (τ.G.obj q.1 : Type)) ⟨(p.1, U'), Prod.mkHom p.2 g⟩
  ev_map {U U₁ U'} g f v := funext fun p ↦ by
    have e : (CategoryTheory.Prod.sectR T D).map g ≫ Prod.mkHom p.2 f = Prod.mkHom p.2 (g ≫ f) := Subsingleton.elim _ _
    show (v : ∀ q : (Σ y : C × D, ((T, U) ⟶ y)), τ.G.obj q.1) ⟨(p.1, U'), (CategoryTheory.Prod.sectR T D).map g ≫ Prod.mkHom p.2 f⟩ =
      (v : ∀ q : (Σ y : C × D, ((T, U) ⟶ y)), τ.G.obj q.1) ⟨(p.1, U'), Prod.mkHom p.2 (g ≫ f)⟩
    rw [e]
  ext {U} v h := funext fun p ↦ by
    obtain ⟨⟨T', U'⟩, f⟩ := p
    have h2 := congrFun (h U' f.2) ⟨T', f.1⟩
    exact h2
  ex {U} b := ⟨fun p ↦ b p.1.2 p.2.2 ⟨p.1.1, p.2.1⟩, fun _ _ ↦ rfl⟩

theorem aug_up_ex [Quiver.IsThin C] [Quiver.IsThin D] (T : C) (k : ℕ) : (τ.up.aug T).Ex k := by
  match k with
  | 0 =>
    refine Cx.ex_zero_iff.2 fun j hj ↦ funext fun p ↦ funext fun U ↦ ?_
    have h := congrFun (congrFun hj (pt U)) ⟨(p.1, U), Prod.mkHom p.2 (𝟙 U)⟩
    exact h
  | 1 =>
    refine Cx.ex_succ_iff.2 fun a ha ↦ ?_
    refine ⟨fun p U ↦ (τ.fibD T).ev (𝟙 U) ((a : MCn (τ.up.fibG T) 0) (pt U)) ⟨p.1, p.2⟩, ?_⟩
    funext c
    refine (τ.fibD T).ev_inj fun U' g ↦ ?_
    rw [(τ.fibD T).key a ha c g]
    refine funext fun p ↦ ?_
    rfl
  | k + 2 => exact Cx.ex_succ_iff.2 fun a ha ↦ (τ.fibD T).exact k a ha

theorem cone_up [Quiver.IsThin C] [Quiver.IsThin D] (k : ℕ) : (cone τ.up.pull).Ex k := by
  have hA : ∀ k, (cn τ.J).Ex (k + 1) := fun k ↦ Cx.ex_succ_iff.2 fun a ha ↦
    (coindD fun T ↦ ModuleCat.of R (∀ U : D, τ.G.obj (T, U))).exact k a ha
  have hB : ∀ k, (cn τ.I).Ex (k + 1) := fun k ↦ Cx.ex_succ_iff.2 fun a ha ↦ (coindD τ.G.obj).exact k a ha
  refine cone_ex_of_acyclic (A := cn τ.J) (B := cn τ.I) τ.up.pull hA hB ?_ ?_ k
  · intro a ha h
    refine (coindD fun T ↦ ModuleCat.of R (∀ U : D, τ.G.obj (T, U))).zero_ext a ha fun T' ↦ funext fun U ↦ ?_
    exact congrFun (congrFun h (pt (T', U))) ⟨(T', U), 𝟙 _⟩
  · intro b hb
    obtain ⟨a, ha, hab⟩ := (coindD (fun T ↦ ModuleCat.of R (∀ U : D, τ.G.obj (T, U)))).zero_ex
      (fun T' U ↦ (coindD τ.G.obj).ev (𝟙 _) ((b : MCn τ.I 0) (pt (T', U))))
    refine ⟨a, ha, ?_⟩
    have h1 : τ.up.pull.f 1 ((cn τ.J).d 0 a) = (cn τ.I).d 0 (τ.up.pull.f 0 a) := τ.up.pull.f_d 0 a
    have h2 : (cn τ.J).d 0 a = 0 := ha
    rw [h2, map_zero] at h1
    exact (coindD τ.G.obj).uniq _ _ h1.symm hb fun y ↦ congrFun (hab y.1) y.2

end Tr

end Main

section Assembly

variable {C D : Type} [Category.{0} C] [Category.{0} D]

namespace Tr

variable (τ : Tr R C D)

theorem ηF_inj (h : ∀ T, Function.Injective (τ.fib T)) (T : C) : Function.Injective (τ.ηF.app T).hom := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  apply (injective_iff_map_eq_zero _).1 (h T)
  funext c
  have h1 : (τ.α.app (T, c.obj (Fin.last 0))).hom ((τ.F.map (𝟙 T)).hom v) = 0 :=
    congrFun (congrFun hv ⟨T, 𝟙 T⟩) (c.obj (Fin.last 0))
  rw [τ.F.map_id] at h1
  exact h1

theorem ηF_pt (h : ∀ T, Function.Injective (τ.fib T)) : PtSES τ.ηF (cokerπ τ.ηF) :=
  ptSES_coker (τ.ηF_inj h)

theorem ηG_pt : PtSES τ.ηG (cokerπ τ.ηG) := ptSES_coker (coindη_inj τ.G)

def coneSES (h : ∀ T, Function.Injective (τ.fib T)) :
    SES (cone τ.pull) (cone τ.up.pull) (cone τ.quo.pull) :=
  SES.cone (cnSES (τ.ηF_pt h)) (cnSES τ.ηG_pt) τ.pull τ.up.pull τ.quo.pull
    (fun n f ↦ funext fun c ↦ τ.comm _ _) (fun n f ↦ rfl)

theorem ptFib (T : C) : PtSES (Functor.whiskerLeft (CategoryTheory.Prod.sectR T D) τ.ηG)
    (Functor.whiskerLeft (CategoryTheory.Prod.sectR T D) (cokerπ τ.ηG)) where
  inj x := τ.ηG_pt.inj _
  ex x := τ.ηG_pt.ex _
  surj x := τ.ηG_pt.surj _

def augSES (h : ∀ T, Function.Injective (τ.fib T)) (T : C) : SES (τ.aug T) (τ.up.aug T) (τ.quo.aug T) where
  i :=
    { f
        | 0 => (τ.ηF.app T).hom
        | k + 1 => (post (Functor.whiskerLeft (CategoryTheory.Prod.sectR T D) τ.ηG)).f k
      f_d
        | 0, x => funext fun c ↦ (τ.comm (T, c.obj (Fin.last 0)) x).symm
        | k + 1, x => (post (Functor.whiskerLeft (CategoryTheory.Prod.sectR T D) τ.ηG)).f_d k x }
  p :=
    { f
        | 0 => (cokerπ τ.ηF |>.app T).hom
        | k + 1 => (post (Functor.whiskerLeft (CategoryTheory.Prod.sectR T D) (cokerπ τ.ηG))).f k
      f_d
        | 0, x => rfl
        | k + 1, x => (post (Functor.whiskerLeft (CategoryTheory.Prod.sectR T D) (cokerπ τ.ηG))).f_d k x }
  inj
    | 0 => (τ.ηF_pt h).inj T
    | k + 1 => (cnSES (τ.ptFib T)).inj k
  ex
    | 0 => (τ.ηF_pt h).ex T
    | k + 1 => (cnSES (τ.ptFib T)).ex k
  surj
    | 0 => (τ.ηF_pt h).surj T
    | k + 1 => (cnSES (τ.ptFib T)).surj k

end Tr

theorem cone_ex [Quiver.IsThin C] [Quiver.IsThin D] (k : ℕ) :
    ∀ τ : Tr R C D, (∀ T j, (τ.aug T).Ex j) → (cone τ.pull).Ex k := by
  induction k with
  | zero =>
    intro τ h
    exact (τ.coneSES fun T ↦ h T 0).ex_zero (τ.cone_up 0)
  | succ k ih =>
    intro τ h
    have h0 : ∀ T, Function.Injective (τ.fib T) := fun T ↦ h T 0
    refine (τ.coneSES h0).ex_succ τ.cone_up (ih τ.quo fun T j ↦ ?_)
    exact (τ.augSES h0 T).ex_quot (h T) (τ.aug_up_ex T) j

end Assembly

section Bridge

open GlobalTheory.CatCoh MainStatements.Hodge

variable {C D : Type} [Category.{0} C] [Category.{0} D]

def modOf (F : C ⥤ CommAlgCat.{0} R) : C ⥤ ModuleCat.{0} R where
  obj T := ModuleCat.of R (F.obj T)
  map φ := ModuleCat.ofHom (mp F φ).toLinearMap
  map_id T := ModuleCat.hom_ext (LinearMap.ext fun b ↦ mp_id F T b)
  map_comp φ ψ := ModuleCat.hom_ext (LinearMap.ext fun b ↦ mp_comp F φ ψ b)

theorem mdn_modOf (F : C ⥤ CommAlgCat.{0} R) (n : ℕ) (f : Cn F n) : mdn (modOf F) n f = dn F n f := rfl

def trOf {F : C ⥤ CommAlgCat.{0} R} {G : C × D ⥤ CommAlgCat.{0} R} (m : Proj F G) : Tr R C D where
  F := modOf F
  G := modOf G
  α :=
    { app := fun x ↦ ModuleCat.ofHom (m.α x).toLinearMap
      naturality := fun x x' φ ↦ ModuleCat.hom_ext (LinearMap.ext fun b ↦ m.naturality φ b) }

end Bridge

section Final

theorem qiso_of_cone {A B : Cx R} (f : Hm A B) (h : ∀ k, (cone f).Ex k) :
    (∀ a, A.d 0 a = 0 → f.f 0 a = 0 → a = 0) ∧
    (∀ b, B.d 0 b = 0 → ∃ a, A.d 0 a = 0 ∧ f.f 0 a = b) ∧
    (∀ n a, A.d (n + 1) a = 0 → ∀ b, B.d n b = f.f (n + 1) a → ∃ y, A.d n y = a) ∧
    (∀ n z, B.d (n + 1) z = 0 → ∃ x y, A.d (n + 1) x = 0 ∧ f.f (n + 1) x - z = B.d n y) := by
  refine ⟨(cone_ex_zero f).1 (h 0), fun b hb ↦ ?_, fun n a ha b hb ↦ ?_, fun n z hz ↦ ?_⟩
  · exact (cone_ex_one f).1 (h 1) 0 b (map_zero _) (by rw [map_zero, hb])
  · cases n with
    | zero =>
      obtain ⟨y, h1, -⟩ := (cone_ex_one f).1 (h 1) a b ha hb.symm
      exact ⟨y, h1⟩
    | succ k =>
      obtain ⟨y, z, h1, -⟩ := (cone_ex_succ f k).1 (h (k + 2)) a b ha hb.symm
      exact ⟨y, h1⟩
  · obtain ⟨y, w, h1, h2⟩ := (cone_ex_succ f n).1 (h (n + 2)) 0 z (map_zero _) (by rw [map_zero, hz])
    exact ⟨y, w, h1, by rw [← h2]; abel⟩

open MainStatements.Hodge in

theorem fubiniSt : CxSt → FubiniSt := by
  intro _ R _ C _ F D _ _ _ G m h
  have hτ : ∀ T j, ((trOf m).aug T).Ex j := by
    intro T j
    obtain ⟨h1, h2, h3⟩ := h T
    match j with
    | 0 => exact h1
    | 1 => exact h2
    | k + 2 => exact h3 k
  obtain ⟨q1, q2, q3, q4⟩ := qiso_of_cone (trOf m).pull fun k ↦ cone_ex k (trOf m) hτ
  refine ⟨⟨fun x hx hy ↦ ?_, fun z hz ↦ ?_⟩, fun n ↦ ⟨fun x hx hy ↦ ?_, fun z hz ↦ ?_⟩⟩
  · obtain ⟨y, hy⟩ := hy
    exact ⟨0, by
      rw [LinearMap.zero_apply]
      exact (q1 x hx hy.symm).symm⟩
  · obtain ⟨x, h1, h2⟩ := q2 z hz
    exact ⟨x, 0, h1, (sub_eq_zero.2 h2)⟩
  · obtain ⟨y, hy⟩ := hy
    exact q3 n x hx y hy
  · exact q4 n z hz

end Final

end GlobalTheory.CompanionTheory.NerveCoh

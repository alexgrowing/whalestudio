import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemBtOrderIffBtSetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionIffSectionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExtensionOrderEqSpanStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.FlatBC

section Alg

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']

lemma tensor_frac_form (u : R' ⊗[R] FractionRing R) :
    ∃ (r : R') (d : R), d ≠ 0 ∧ u = r ⊗ₜ[R] (algebraMap R (FractionRing R) d)⁻¹ := by
  have hne : ∀ d : R, d ≠ 0 → algebraMap R (FractionRing R) d ≠ 0 := fun d hd => by
    simpa using hd
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul r k =>
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    refine ⟨a • r, d, nonZeroDivisors.ne_zero hd, ?_⟩
    rw [TensorProduct.smul_tmul, div_eq_mul_inv, Algebra.smul_def]
  | add x y hx hy =>
    obtain ⟨r₁, d₁, h₁, rfl⟩ := hx
    obtain ⟨r₂, d₂, h₂, rfl⟩ := hy
    refine ⟨d₂ • r₁ + d₁ • r₂, d₁ * d₂, mul_ne_zero h₁ h₂, ?_⟩
    have i₁ := hne d₁ h₁
    have i₂ := hne d₂ h₂
    rw [TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
    congr 2 <;> (simp only [Algebra.smul_def, map_mul]; field_simp)

def kapL (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    FractionRing R →ₗ[R] FractionRing R' where
  toFun := κ
  map_add' := map_add κ
  map_smul' r x := by
    have := congr($hκ r)
    simp only [RingHom.comp_apply] at this
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply, this,
      IsScalarTower.algebraMap_apply R R' (FractionRing R')]

lemma inj_one (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    Function.Injective ((kapL κ hκ).liftBaseChange R') := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨r, d, hd, rfl⟩ := tensor_frac_form u
  rw [LinearMap.liftBaseChange_tmul] at hu
  have h1 : algebraMap R (FractionRing R) d ≠ 0 := by simpa using hd
  have h2 : κ (algebraMap R (FractionRing R) d)⁻¹ ≠ 0 :=
    (map_ne_zero κ).2 (inv_ne_zero h1)
  have h3 : r = 0 := by
    have h4 : algebraMap R' (FractionRing R') r * κ (algebraMap R (FractionRing R) d)⁻¹ = 0 := by
      rw [← Algebra.smul_def]; exact hu
    have := (mul_eq_zero.1 h4).resolve_right h2
    simpa using this
  simp [h3]

lemma inj_pi {T : Type} [Fintype T] [DecidableEq T] (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    Function.Injective (((kapL κ hκ).compLeft T).liftBaseChange R') := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have key : ∀ (y : R' ⊗[R] (T → FractionRing R)) (h : T),
      (kapL κ hκ).liftBaseChange R' (TensorProduct.piRight R R' R' (fun _ : T => FractionRing R) y h) =
        (((kapL κ hκ).compLeft T).liftBaseChange R' y) h := by
    intro y h
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r f => simp [TensorProduct.piRight_apply, LinearMap.liftBaseChange_tmul]
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  apply (TensorProduct.piRight R R' R' (fun _ : T => FractionRing R)).injective
  rw [map_zero]
  funext h
  apply inj_one κ hκ
  rw [key, hy]
  simp

lemma tensor_pi_ext {T Q : Type} [Fintype T] [DecidableEq T] [AddCommGroup Q] [Module R Q]
    (y : R' ⊗[R] (T → Q)) (h : ∀ t, (LinearMap.proj t : (T → Q) →ₗ[R] Q).lTensor R' y = 0) : y = 0 := by
  have key : ∀ (y : R' ⊗[R] (T → Q)) (t : T),
      TensorProduct.piRight R R' R' (fun _ : T => Q) y t =
        (LinearMap.proj t : (T → Q) →ₗ[R] Q).lTensor R' y := by
    intro y t
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r f => simp [TensorProduct.piRight_apply]
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  apply (TensorProduct.piRight R R' R' (fun _ : T => Q)).injective
  rw [map_zero]
  funext t
  rw [key, h]
  rfl

theorem alg_core {T : Type} [CommGroup T] [Finite T] [Module.Flat R R']
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R'))
    (N : Submodule R (T → FractionRing R)) (M : Submodule R (T → R))
    (hM : ∀ f, f ∈ M ↔ ∀ t, (fun h => algebraMap R (FractionRing R) (f (t * h))) ∈ N)
    (g : T → R')
    (hg : ∀ t, (fun h => algebraMap R' (FractionRing R') (g (t * h))) ∈
      Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ N, w = fun h => κ (n h)}) :
    g ∈ Submodule.span R' {g : T → R' | ∃ f ∈ M, g = fun t => algebraMap R R' (f t)} := by
  classical
  cases nonempty_fintype T
  let a : T → ((T → R) →ₗ[R] (T → FractionRing R)) := fun t =>
    ((Algebra.linearMap R (FractionRing R)).compLeft T) ∘ₗ (LinearMap.funLeft R R (fun h => t * h))
  have ha : ∀ t f h, a t f h = algebraMap R (FractionRing R) (f (t * h)) := fun _ _ _ => rfl
  let b : (T → R) →ₗ[R] (T → (T → FractionRing R) ⧸ N) := LinearMap.pi fun t => N.mkQ ∘ₗ a t
  have hex : Function.Exact M.subtype b := by
    intro f
    constructor
    · intro hf
      have hfM : f ∈ M := (hM f).2 fun t => by
        have h1 : N.mkQ (a t f) = 0 := congrFun hf t
        exact (Submodule.Quotient.mk_eq_zero N).1 h1
      exact ⟨⟨f, hfM⟩, rfl⟩
    · rintro ⟨m, rfl⟩
      funext t
      exact (Submodule.Quotient.mk_eq_zero N).2 ((hM _).1 m.2 t)
  have hexS := Module.Flat.lTensor_exact R' hex
  have hexN := Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_mkQ N)
  let z : R' ⊗[R] (T → R) := ∑ h, g h ⊗ₜ[R] (Pi.single h 1 : T → R)
  let cW := ((kapL κ hκ).compLeft T).liftBaseChange R'
  have hc : ∀ t, cW ((a t).lTensor R' z) =
      fun h => algebraMap R' (FractionRing R') (g (t * h)) := by
    intro t
    funext h
    simp only [z, map_sum, LinearMap.lTensor_tmul, cW, LinearMap.liftBaseChange_tmul, Finset.sum_apply,
      Pi.smul_apply]
    rw [Finset.sum_eq_single (t * h)]
    · have := congr($hκ 1)
      simp [LinearMap.compLeft_apply, ha, kapL, Algebra.smul_def]
    · intro b' _ hb'
      simp [LinearMap.compLeft_apply, ha, kapL, Ne.symm hb']
    · simp
  have hN : ∀ t, ∃ y : R' ⊗[R] N, cW (N.subtype.lTensor R' y) =
      fun h => algebraMap R' (FractionRing R') (g (t * h)) := by
    intro t
    let cN := (((kapL κ hκ).compLeft T) ∘ₗ N.subtype).liftBaseChange R'
    have e1 : ∀ y, cN y = cW (N.subtype.lTensor R' y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r n => simp [cN, cW, LinearMap.liftBaseChange_tmul]
      | add p q hp hq => simp only [map_add, hp, hq]
    have hle : Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ N, w = fun h => κ (n h)} ≤
        LinearMap.range cN := by
      rw [Submodule.span_le]
      rintro _ ⟨n, hn, rfl⟩
      refine ⟨(1 : R') ⊗ₜ[R] (⟨n, hn⟩ : N), ?_⟩
      simp only [cN, LinearMap.liftBaseChange_tmul, one_smul]
      rfl
    obtain ⟨y, hy⟩ := hle (hg t)
    exact ⟨y, by rw [← e1, hy]⟩
  have hz : b.lTensor R' z = 0 := by
    apply tensor_pi_ext
    intro t
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have e2 : (LinearMap.proj t : (T → (T → FractionRing R) ⧸ N) →ₗ[R] _) ∘ₗ b = N.mkQ ∘ₗ a t := rfl
    rw [e2, LinearMap.lTensor_comp, LinearMap.comp_apply]
    obtain ⟨y, hy⟩ := hN t
    have e3 : (a t).lTensor R' z = N.subtype.lTensor R' y :=
      inj_pi κ hκ ((hc t).trans hy.symm)
    rw [e3]
    exact (hexN _).2 ⟨y, rfl⟩
  obtain ⟨y, hy⟩ := (hexS z).1 hz
  let e := ((Algebra.linearMap R R').compLeft T).liftBaseChange R'
  have hez : e z = g := by
    funext h
    simp only [z, e, map_sum, LinearMap.liftBaseChange_tmul, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single h]
    · simp [LinearMap.compLeft_apply]
    · intro b' _ hb'
      simp [LinearMap.compLeft_apply, Ne.symm hb']
    · simp
  have hall : ∀ y : R' ⊗[R] M, e (M.subtype.lTensor R' y) ∈
      Submodule.span R' {g : T → R' | ∃ f ∈ M, g = fun t => algebraMap R R' (f t)} := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
      simp only [LinearMap.lTensor_tmul, e, LinearMap.liftBaseChange_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, m.2, rfl⟩)
    | add p q hp hq =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hp hq
  rw [← hez, ← hy]
  exact hall y

end Alg

section Sch

lemma top_le_pre {X Y : Scheme.{0}} (x : X ⟶ Y) : (⊤ : X.Opens) ≤ x ⁻¹ᵁ ⊤ := by simp

lemma valAt_congr {B : Type} [CommRing B] {X : Scheme.{0}} {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) : valAt x U h s = valAt y U h' s := by
  subst e; rfl

lemma valAt_add {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (s s' : Γ(X, U)) :
    valAt x U h (s + s') = valAt x U h s + valAt x U h s' := by
  simp [valAt]

lemma valAt_mul {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (s s' : Γ(X, U)) :
    valAt x U h (s * s') = valAt x U h s * valAt x U h s' := by
  simp [valAt]

lemma valAt_zero {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt x U h 0 = 0 := by
  simp [valAt]

lemma valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Y) (f : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (x ≫ f) U h' s = valAt x V h ((f.appLE U V hV).hom s) := by
  simp only [valAt]
  rw [← Scheme.Hom.appLE_comp_appLE x f U V ⊤ hV h]
  rfl

lemma valAt_spec {A B : Type} [CommRing A] [CommRing B] (κ : A →+* B)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ)) ⁻¹ᵁ ⊤) (c : Γ(Spec (CommRingCat.of A), ⊤)) :
    valAt (Spec.map (CommRingCat.ofHom κ)) ⊤ h c = κ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) := by
  have e : (Spec.map (CommRingCat.ofHom κ)).appLE ⊤ ⊤ h = (Spec.map (CommRingCat.ofHom κ)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  simp only [valAt]
  rw [e]
  have := congr(($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom κ))).hom c)
  exact this

lemma valAt_map {A B : Type} [CommRing A] [CommRing B] (κ : A →+* B) {X : Scheme.{0}}
    (y : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ y) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ y) U h' s = κ (valAt y U h s) := by
  rw [valAt_comp _ y U ⊤ h (top_le_pre _), valAt_spec]
  rfl

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

lemma valAt_const (Γ : QFGroup R T) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤) (h' : ⊤ ≤ Γ.G.hom ⁻¹ᵁ ⊤)
    (c : Γ(Spec (CommRingCat.of R), ⊤)) :
    valAt (Γ.pt t).left ⊤ h ((Γ.G.hom.appLE ⊤ ⊤ h').hom c) =
      algebraMap R (FractionRing R) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) := by
  have e : (Γ.pt t).left ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    Over.w (Γ.pt t)
  rw [← valAt_comp (Γ.pt t).left Γ.G.hom ⊤ ⊤ h' h (top_le_pre _), valAt_congr e _ _ (top_le_pre _), valAt_spec]

def secFn (Γ : QFGroup R T) : Submodule R (T → FractionRing R) where
  carrier := {f | ∃ s : Γ(Γ.G.left, ⊤), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ ⊤),
    valAt (Γ.pt t).left ⊤ h s = f t}
  add_mem' := by
    rintro f f' ⟨s, hs⟩ ⟨s', hs'⟩
    exact ⟨s + s', fun t h => by rw [valAt_add, hs, hs']; rfl⟩
  zero_mem' := ⟨0, fun t h => by rw [valAt_zero]; rfl⟩
  smul_mem' := by
    rintro r f ⟨s, hs⟩
    refine ⟨(Γ.G.hom.appLE ⊤ ⊤ (top_le_pre _)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) * s,
      fun t h => ?_⟩
    rw [valAt_mul, valAt_const, hs]
    simp [Algebra.smul_def]

lemma mem_btOrder_iff [Finite T] (Γ : QFGroup R T) (f : T → R) :
    f ∈ Γ.btOrder ⊤ ↔ ∀ t, (fun h => algebraMap R (FractionRing R) (f (t * h))) ∈ secFn Γ := by
  rw [GlobalTheory.T.mem_btOrder_iff_btSet R T Γ ⊤ f]
  refine forall_congr' fun t => ?_
  have := GlobalTheory.T.regular_function_iff_section R T Γ ⊤ (fun h => algebraMap R (FractionRing R) (f (t * h)))
  exact this

lemma pushout_induction {A B C D : CommRingCat.{0}} {a : A ⟶ B} {c : A ⟶ C} {b : B ⟶ D} {d : C ⟶ D}
    (h : IsPushout a c b d) (P : D → Prop) (h0 : P 0) (h1 : ∀ x, P (b.hom x))
    (h2 : ∀ s n, P n → P (d.hom s * n)) (h3 : ∀ x y, P x → P y → P (x + y)) (x : D) : P x := by
  letI : Algebra A B := a.hom.toAlgebra
  letI : Algebra A C := c.hom.toAlgebra
  letI : Algebra B D := b.hom.toAlgebra
  letI : Algebra C D := d.hom.toAlgebra
  letI : Algebra A D := (a ≫ b).hom.toAlgebra
  haveI : IsScalarTower A B D := .of_algebraMap_eq fun r => rfl
  haveI : IsScalarTower A C D := .of_algebraMap_eq fun r => congr($(h.w).hom r)
  have hpo : Algebra.IsPushout A C B D := CommRingCat.isPushout_iff_isPushout.mp h.flip
  induction x using hpo.out.inductionOn with
  | zero => exact h0
  | tmul y => exact h1 y
  | smul s n hn => exact h2 s n hn
  | add x y hx hy => exact h3 x y hx hy

variable {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R']

theorem val_mem_span [Finite T] [Module.Flat R R'] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R'))
    (x : Γ(Γ'.G.left, ⊤)) :
    (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) x) ∈
      Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ secFn Γ, w = fun h => κ (n h)} := by
  haveI := Γ.quasiCompact
  haveI := Γ.separated
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have H := hbc.cart
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) (top_le_pre _) (top_le_pre _)
    (by simp)).1 (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) (Γ.G.hom.isCompact_preimage (isAffineOpen_top _).isCompact)
      (Γ.G.hom.isQuasiSeparated_preimage (isAffineOpen_top _).isQuasiSeparated))
  refine pushout_induction po (fun y => (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) y) ∈
      Submodule.span R' {w : T → FractionRing R' | ∃ n ∈ secFn Γ, w = fun h => κ (n h)}) ?_ ?_ ?_ ?_ x
  · have : (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) (0 : Γ(Γ'.G.left, ⊤))) = 0 := by
      funext t; exact valAt_zero _ _ _
    rw [this]
    exact Submodule.zero_mem _
  · intro s
    refine Submodule.subset_span ⟨fun t => valAt (Γ.pt t).left ⊤ (top_le_pre _) s, ⟨s, fun _ _ => rfl⟩, ?_⟩
    funext t
    rw [← valAt_comp (Γ'.pt t).left F ⊤ ⊤ _ (top_le_pre _) (top_le_pre _),
      valAt_congr (GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hbc κ hκ t) _ _ (top_le_pre _),
      valAt_map κ _ _ (top_le_pre _)]
  · intro c n hn
    have : (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) (((Γ'.G.hom.appLE ⊤ ⊤ (top_le_pre _)).hom c) * n)) =
        ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom c) •
          (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) n) := by
      funext t
      rw [valAt_mul, valAt_const]
      simp [Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ hn
  · intro p q hp hq
    have : (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) (p + q)) =
        (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) p) + (fun t => valAt (Γ'.pt t).left ⊤ (top_le_pre _) q) := by
      funext t
      exact valAt_add _ _ _ _ _
    rw [this]
    exact Submodule.add_mem _ hp hq

lemma flat_inj [Module.Flat R R'] : Function.Injective (algebraMap R R') := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have hreg : IsSMulRegular R' r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr0)
  have h1 : r • (1 : R') = r • (0 : R') := by rw [Algebra.smul_def, hr]; simp
  exact one_ne_zero (hreg h1)

lemma exists_kappa (hφ : Function.Injective (algebraMap R R')) :
    ∃ κ : FractionRing R →+* FractionRing R',
      κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') := by
  have hinj : Function.Injective ((algebraMap R' (FractionRing R')).comp (algebraMap R R')) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hφ
  refine ⟨IsFractionRing.lift (K := FractionRing R) hinj, ?_⟩
  apply RingHom.ext
  intro r
  exact IsFractionRing.lift_algebraMap (K := FractionRing R) hinj r

lemma btOrder_le_ext [Finite T] [Module.Flat R R'] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    Γ'.btOrder ⊤ ≤ extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  intro g hg
  rw [GlobalTheory.T.extension_order_eq_span]
  refine alg_core κ hκ (secFn Γ) (Subalgebra.toSubmodule (Γ.btOrder ⊤)) (fun f => mem_btOrder_iff Γ f) g ?_
  intro t
  obtain ⟨x, hx⟩ := (mem_btOrder_iff Γ' g).1 hg t
  have e : (fun h => algebraMap R' (FractionRing R') (g (t * h))) =
      fun h => valAt (Γ'.pt h).left ⊤ (top_le_pre _) x := by
    funext h
    exact (hx h _).symm
  rw [e]
  exact val_mem_span Γ Γ' F hbc κ hκ x

lemma ext_le_btOrder [Finite T] (Γ : QFGroup R T) (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hbc : Γ'.IsBaseChange Γ (algebraMap R R') F)
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R')) :
    extOrder (algebraMap R R') (Γ.btOrder ⊤) ≤ Γ'.btOrder ⊤ := by
  have hκ' : ∀ r, κ (algebraMap R _ r) = algebraMap R' (FractionRing R') (algebraMap R R' r) :=
    fun r => congr($hκ r)
  refine Algebra.adjoin_le ?_
  rintro _ ⟨f, hf, rfl⟩
  refine (mem_btOrder_iff Γ' _).2 fun t => ?_
  obtain ⟨s, hs⟩ := (mem_btOrder_iff Γ f).1 hf t
  refine ⟨(F.appLE ⊤ ⊤ (top_le_pre _)).hom s, fun h hh => ?_⟩
  rw [← valAt_comp (Γ'.pt h).left F ⊤ ⊤ _ _ (top_le_pre _),
    valAt_congr (GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hbc κ hκ h) _ _ (top_le_pre _),
    valAt_map κ _ _ (top_le_pre _), hs h, hκ']

end Sch

theorem btOrder_flat_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → Γ'.btOrder ⊤ = extOrder (algebraMap R R') (Γ.btOrder ⊤) := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hbc hflat
  obtain ⟨κ, hκ⟩ := exists_kappa (flat_inj (R := R) (R' := R'))
  exact le_antisymm (btOrder_le_ext Γ Γ' F hbc κ hκ) (ext_le_btOrder Γ Γ' F hbc κ hκ)

end GlobalTheory.CompanionTheory.Ar.BT.FlatBC

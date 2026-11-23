import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MilFlat

open TensorProduct

theorem isPullback_iff_elem {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (w : f ≫ h = g ≫ i) :
    IsPullback f g h i ↔ (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  constructor
  · intro H
    have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
    exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩
  · rintro ⟨h₁, h₂⟩
    refine IsPullback.of_map (forget CommRingCat) w ((Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩)
    · ext x
      simpa using congrArg (fun φ : A ⟶ D ↦ φ.hom x) w
    · exact fun x y hxy ↦ h₁ x y hxy.1 hxy.2
    · exact fun b c hbc ↦ h₂ b c hbc

theorem isoIsPushout_tmul {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {X : CommRingCat.{0}} {f : CommRingCat.of A ⟶ X} {f' : CommRingCat.of B ⟶ X}
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R B)) f f') (a : A) (b : B) :
    ((CommRingCat.isPushout_tensorProduct R A B).isoIsPushout _ _ h).hom.hom (a ⊗ₜ b) = f.hom a * f'.hom b := by
  have e₁ := congrArg (fun φ ↦ φ.hom a)
    (IsPushout.inl_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A B) h)
  have e₂ := congrArg (fun φ ↦ φ.hom b)
    (IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct R A B) h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₁ e₂
  have : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by simp
  rw [this, map_mul]
  simp only [Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply] at e₁ e₂
  exact congrArg₂ (· * ·) e₁ e₂

theorem isPullback_of_flat (P C₁ C₂ C₀ E E₁ E₂ E₀ : CommRingCat.{0}) (p₁ : P ⟶ C₁) (p₂ : P ⟶ C₂) (q₁ : C₁ ⟶ C₀)
    (q₂ : C₂ ⟶ C₀) (hP : IsPullback p₁ p₂ q₁ q₂) (hq : Function.Surjective q₂.hom) (g : P ⟶ E) (g₁ : C₁ ⟶ E₁)
    (g₂ : C₂ ⟶ E₂) (g₀ : C₀ ⟶ E₀) (i₁ : E ⟶ E₁) (i₂ : E ⟶ E₂) (r₁ : E₁ ⟶ E₀) (r₂ : E₂ ⟶ E₀) (hg : g.hom.Flat)
    (h₁ : IsPushout g p₁ i₁ g₁) (h₂ : IsPushout g p₂ i₂ g₂) (h₀ : IsPushout g₂ q₂ r₂ g₀)
    (w₁ : i₁ ≫ r₁ = i₂ ≫ r₂) (w₂ : g₁ ≫ r₁ = q₁ ≫ g₀) : IsPullback i₁ i₂ r₁ r₂ := by
  letI : Algebra P E := g.hom.toAlgebra
  letI : Algebra P C₁ := p₁.hom.toAlgebra
  letI : Algebra P C₂ := p₂.hom.toAlgebra
  letI : Algebra P C₀ := (p₂ ≫ q₂).hom.toAlgebra
  haveI : Module.Flat P E := hg
  have hw : ∀ a, q₁.hom (p₁.hom a) = q₂.hom (p₂.hom a) := fun a ↦ by
    simpa using congrArg (fun φ ↦ φ.hom a) hP.w
  have hw₁ : ∀ x, r₁.hom (i₁.hom x) = r₂.hom (i₂.hom x) := fun x ↦ by
    simpa using congrArg (fun φ ↦ φ.hom x) w₁
  have hw₂ : ∀ c, r₁.hom (g₁.hom c) = g₀.hom (q₁.hom c) := fun c ↦ by
    simpa using congrArg (fun φ ↦ φ.hom c) w₂
  have hw₀ : ∀ c, r₂.hom (g₂.hom c) = g₀.hom (q₂.hom c) := fun c ↦ by
    simpa using congrArg (fun φ ↦ φ.hom c) h₀.w
  obtain ⟨hinj, hex⟩ := (isPullback_iff_elem p₁ p₂ q₁ q₂ hP.w).1 hP

  let f : P →ₗ[P] C₁ × C₂ := (Algebra.linearMap P C₁).prod (Algebra.linearMap P C₂)
  let Q₁ : C₁ →ₗ[P] C₀ :=
    { toFun := q₁.hom, map_add' := map_add _
      map_smul' := fun a c ↦ by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, hw] }
  let Q₂ : C₂ →ₗ[P] C₀ :=
    { toFun := q₂.hom, map_add' := map_add _
      map_smul' := fun a c ↦ by
        simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }
  let h : C₁ × C₂ →ₗ[P] C₀ := Q₁ ∘ₗ LinearMap.fst P C₁ C₂ - Q₂ ∘ₗ LinearMap.snd P C₁ C₂
  have hh : ∀ x y, h (x, y) = q₁.hom x - q₂.hom y := fun _ _ ↦ rfl
  have hf : ∀ a, f a = (p₁.hom a, p₂.hom a) := fun _ ↦ rfl
  have hfinj : Function.Injective f := fun a b hab ↦ by
    rw [hf, hf, Prod.ext_iff] at hab
    exact hinj a b hab.1 hab.2
  have hexact : Function.Exact f h := by
    rintro ⟨x, y⟩
    rw [hh, sub_eq_zero]
    constructor
    · intro hxy
      obtain ⟨a, ha₁, ha₂⟩ := hex x y hxy
      exact ⟨a, by rw [hf, ha₁, ha₂]⟩
    · rintro ⟨a, ha⟩
      rw [hf, Prod.mk.injEq] at ha
      rw [← ha.1, ← ha.2]
      exact hw a
  have hsurj : Function.Surjective h := fun z ↦ by
    obtain ⟨y, hy⟩ := hq (-z)
    exact ⟨(0, y), by rw [hh, hy]; simp⟩
  have hex' := lTensor_exact E hexact hsurj
  have hinj' := Module.Flat.lTensor_preserves_injective_linearMap (M := E) f hfinj

  have h₀' : IsPushout g (p₂ ≫ q₂) (i₂ ≫ r₂) g₀ := (h₂.flip.paste_horiz h₀.flip).flip
  let k₁ := (CommRingCat.isPushout_tensorProduct P E C₁).isoIsPushout _ _ h₁
  let k₂ := (CommRingCat.isPushout_tensorProduct P E C₂).isoIsPushout _ _ h₂
  let k₀ := (CommRingCat.isPushout_tensorProduct P E C₀).isoIsPushout _ _ h₀'
  have k₁t : ∀ (e : E) (c : C₁), k₁.hom.hom (e ⊗ₜ c) = i₁.hom e * g₁.hom c := isoIsPushout_tmul h₁
  have k₂t : ∀ (e : E) (c : C₂), k₂.hom.hom (e ⊗ₜ c) = i₂.hom e * g₂.hom c := isoIsPushout_tmul h₂
  have k₀t : ∀ (e : E) (c : C₀), k₀.hom.hom (e ⊗ₜ c) = r₂.hom (i₂.hom e) * g₀.hom c := isoIsPushout_tmul h₀'
  have kinv : ∀ {X Y : CommRingCat.{0}} (k : X ≅ Y) (y : Y), k.hom.hom (k.inv.hom y) = y := fun k y ↦ by simp
  have kinj : ∀ {X Y : CommRingCat.{0}} (k : X ≅ Y), Function.Injective k.hom.hom := fun k x y hxy ↦ by
    simpa using congrArg k.inv.hom hxy
  let pr := TensorProduct.prodRight P P E C₁ C₂
  have key : ∀ x, k₀.hom.hom (h.lTensor E x) =
      r₁.hom (k₁.hom.hom (pr x).1) - r₂.hom (k₂.hom.hom (pr x).2) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul e c =>
      obtain ⟨c₁, c₂⟩ := c
      rw [LinearMap.lTensor_tmul, hh, TensorProduct.prodRight_tmul, k₀t, k₁t, k₂t, map_mul, map_mul, hw₁, hw₂,
        hw₀, map_sub]
      ring
    | add x y hx hy =>
      simp only [map_add, Prod.fst_add, Prod.snd_add, hx, hy]
      ring
  have keyone : ∀ e : E, pr (f.lTensor E (e ⊗ₜ 1)) = (e ⊗ₜ 1, e ⊗ₜ 1) := fun e ↦ by
    rw [LinearMap.lTensor_tmul, hf, map_one, map_one, TensorProduct.prodRight_tmul]
  have k₁one : ∀ e, k₁.hom.hom (e ⊗ₜ 1) = i₁.hom e := fun e ↦ by rw [k₁t, map_one, _root_.mul_one]
  have k₂one : ∀ e, k₂.hom.hom (e ⊗ₜ 1) = i₂.hom e := fun e ↦ by rw [k₂t, map_one, _root_.mul_one]
  refine (isPullback_iff_elem i₁ i₂ r₁ r₂ w₁).2 ⟨fun x y hx hy ↦ ?_, fun a b hab ↦ ?_⟩
  · have : f.lTensor E (x ⊗ₜ 1) = f.lTensor E (y ⊗ₜ 1) := by
      apply pr.injective
      rw [keyone, keyone, Prod.mk.injEq]
      exact ⟨kinj k₁ (by rw [k₁one, k₁one, hx]), kinj k₂ (by rw [k₂one, k₂one, hy])⟩
    simpa using congrArg (TensorProduct.rid P E) (hinj' this)
  · obtain ⟨x, hxd⟩ : ∃ x, pr x = (k₁.inv.hom a, k₂.inv.hom b) := ⟨pr.symm _, pr.apply_symm_apply _⟩
    have hx0 : h.lTensor E x = 0 := by
      apply kinj k₀
      rw [key, map_zero, hxd, kinv, kinv, hab, sub_self]
    obtain ⟨y, hy⟩ := (hex' x).1 hx0
    have hy' : y = (TensorProduct.rid P E y) ⊗ₜ 1 := by
      rw [← TensorProduct.rid_symm_apply, LinearEquiv.symm_apply_apply]
    rw [hy'] at hy
    have e₁ := congrArg (fun z ↦ k₁.hom.hom (pr z).1) hy
    have e₂ := congrArg (fun z ↦ k₂.hom.hom (pr z).2) hy
    simp only [keyone, k₁one, k₂one, hxd, kinv] at e₁ e₂
    exact ⟨_, e₁, e₂⟩

end GlobalTheory.MilFlat

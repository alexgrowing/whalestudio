import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalMono

theorem coords_eq_zero {O : Type} [CommRing O] [StarRing O] [IsDedekindDomain O]
    [Module.Finite ℤ O] [Module.Free ℤ O] {w : O} (hw : w + star w = 1)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {J : Type} [Fintype J] (ε : Module.Basis J ℤ (PolFan.balForms (star : O → O) X))
    {B : Type} [AddCommGroup B] (c : J → B)
    (hc : ∀ a b, ∑ k, (ε k : LinearMap.BilinForm ℤ X) a b • c k = 0) (k : J) : c k = 0 := by
  classical
  have := Forms.projective_of_int O X
  have := Forms.finite_balTensor (O := O) (X := X)
  have := Forms.free_balTensor (X := X) hw
  let e := Module.Free.chooseBasis ℤ ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel O X)
  have hm := Forms.balTensorMk_mem_balForms O X
  let β : _ → PolFan.balForms (star : O → O) X := fun j =>
    ⟨(Forms.balTensorMk O).compr₂ (e.coord j),
      fun y x => congrArg (e.coord j) (hm.1 y x), fun a y x => congrArg (e.coord j) (hm.2 a y x)⟩
  let L : J → ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel O X) →+ ℤ := fun i =>
    Forms.balTensorLift (O := O) ⟨(ε i : LinearMap.BilinForm ℤ X), (ε i).2.1, (ε i).2.2⟩
  have hL (i a b) : L i (Forms.balTensorMk O a b) = (ε i : LinearMap.BilinForm ℤ X) a b := rfl
  let Φ : ((TensorProduct ℤ X X) ⧸ Forms.balTensorRel O X) →+ B :=
    ∑ i, (zmultiplesHom B (c i)).comp (L i)
  have hΦa (t) : Φ t = ∑ i, L i t • c i := by
    simp [Φ, AddMonoidHom.finsetSum_apply]
  have hΦ : Φ = 0 := Forms.balTensor_hom_ext fun a b => by
    rw [hΦa]
    exact hc a b
  have hε (i) : ε i = ∑ j, L i (e j) • β j := by
    apply Subtype.ext
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [← hL, ← e.sum_repr (Forms.balTensorMk O a b), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_eq_mul, _root_.mul_comm]
    rfl
  have hδ (i) : L i (∑ j, ε.repr (β j) k • e j) = ε.repr (ε i) k := by
    have h1 := congrArg (ε.coord k) (hε i)
    rw [map_sum] at h1
    rw [map_sum, ← ε.coord_apply, h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul, _root_.mul_comm, ε.coord_apply]
  have h := hΦa (∑ j, ε.repr (β j) k • e j)
  simp only [hδ, hΦ, AddMonoidHom.zero_apply] at h
  simpa [Finsupp.single_apply] using h.symm

theorem eq_of_prod_zpow_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (F : Type) [Field F] (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms H.bar X)) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ X) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ X) a b) → x = y := by
  intro E _ _ _ H X _ _ _ _ F _ I _ ε x y hx hy h
  letI : StarRing (𝓞 E) :=
    { star := H.bar
      star_involutive := fun a => by
        apply Subtype.ext
        change ((H.bar (H.bar a) : 𝓞 E) : E) = a
        rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
      star_mul := fun a b => by rw [map_mul, _root_.mul_comm]
      star_add := fun a b => map_add H.bar a b }
  have hw : H.w0 + H.bar H.w0 = 1 := PullbackSections.CVA.cmHostUnit_add_conj_eq_one H
  let u : I → Fˣ := fun i => Units.mk0 (x i) (hx i)
  let v : I → Fˣ := fun i => Units.mk0 (y i) (hy i)
  have huv : ∀ a b, ∏ i, (u i / v i) ^ ((ε i : LinearMap.BilinForm ℤ X) a b) = 1 := by
    intro a b
    rw [Finset.prod_congr rfl (fun i _ => div_zpow _ _ _), Finset.prod_div_distrib, div_eq_one]
    apply Units.ext
    simpa [u, v, Units.coe_prod] using h a b
  funext k
  have hk := coords_eq_zero (O := 𝓞 E) hw ε (fun i => Additive.ofMul (u i / v i))
    (fun a b => by
      apply Additive.toMul.injective
      simp only [toMul_sum, toMul_zsmul, toMul_ofMul, toMul_zero]
      exact huv a b) k
  have hk' : u k / v k = 1 := hk
  simpa [u, v] using congrArg Units.val (div_eq_one.1 hk')

end GlobalTheory.BalMono

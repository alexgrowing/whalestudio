import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ComplexUniformizationSigOne
import Development.AutomorphicArithmetic.RealSpanData.RealData
import Development.AutomorphicArithmetic.RealSpanData.JSpan
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSumBaseChangeOfCommuteBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem actOn_tmul {C V R : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    [CommRing R] [Algebra ℚ R] (rep : C →ₐ[ℚ] Module.End ℚ V) (r s : R) (c : C) (v : V) :
    actOn rep R (r ⊗ₜ c) (s ⊗ₜ v) = (r * s) ⊗ₜ rep c v := by
  have e : actOn rep R (r ⊗ₜ c) = Algebra.ofId R _ r * (Module.End.baseChangeHom ℚ R V) (rep c) :=
    Algebra.TensorProduct.lift_tmul _ _ _ r c
  rw [e]
  change r • ((rep c).baseChange R (s ⊗ₜ v)) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

private theorem actOn_inj {C V R : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    [CommRing R] [Algebra ℚ R] (rep : C →ₐ[ℚ] Module.End ℚ V) (hrep : Function.Injective rep) :
    Function.Injective (actOn rep R) := by
  classical
  have main : ∀ z : R ⊗[ℚ] C, actOn rep R z = 0 → z = 0 := by
    intro z hz
    let bR := Module.Basis.ofVectorSpace ℚ R
    let bC := Module.Basis.ofVectorSpace ℚ C
    let Ψ : (R →ₗ[ℚ] ℚ) → R ⊗[ℚ] C →ₗ[ℚ] C :=
      fun f => (TensorProduct.lid ℚ C).toLinearMap ∘ₗ LinearMap.rTensor C f
    let Φ : (R →ₗ[ℚ] ℚ) → R ⊗[ℚ] V →ₗ[ℚ] V :=
      fun f => (TensorProduct.lid ℚ V).toLinearMap ∘ₗ LinearMap.rTensor V f
    have hΦ : ∀ f (w : R ⊗[ℚ] C) (v : V), Φ f (actOn rep R w (1 ⊗ₜ v)) = rep (Ψ f w) v := by
      intro f w v
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r c => simp [Φ, Ψ, actOn_tmul]
      | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    have hΨ : ∀ f, Ψ f z = 0 := by
      intro f
      apply hrep
      rw [map_zero]
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.zero_apply, ← hΦ, hz, LinearMap.zero_apply, map_zero]
    have hrepr : ∀ (w : R ⊗[ℚ] C) i j,
        (bR.tensorProduct bC).repr w (i, j) = bC.repr (Ψ (bR.coord i) w) j := by
      intro w i j
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r c => simp [Ψ, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]
      | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]
    apply (bR.tensorProduct bC).repr.injective
    ext ⟨i, j⟩
    rw [hrepr, hΨ]
    simp
  intro x y hxy
  rw [← sub_eq_zero]
  apply main
  rw [map_sub, hxy, sub_self]

theorem UpperTheory.commutant_eq_range_actOn_and_injective :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R], (∀ A : Module.End R (R ⊗[ℚ] VQ D), (∀ b : D.O, A ∘ₗ (actQ D b).baseChange R = (actQ D b).baseChange R ∘ₗ A) → ∃ c : R ⊗[ℚ] G.C, actOn L.rep R c = A) ∧ Function.Injective (actOn L.rep R) := by
  intro p _ D G L R _ _
  haveI : Module.Finite ℤ D.La := D.finLa
  refine ⟨fun A hA => ?_, actOn_inj L.rep L.rep_inj⟩
  obtain ⟨k, r, h, hh, hA'⟩ := UpperTheory.exists_sum_baseChange_of_commute_baseChange D.O (VQ D) (VQ D) R (actQ D) (actQ D) A hA
  have hx : ∀ l, ∃ x, L.rep x = h l := fun l => (L.rep_range (h l)).2 (fun b => hh l b)
  choose x hx using hx
  refine ⟨∑ l, r l ⊗ₜ[ℚ] x l, ?_⟩
  rw [hA', map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine TensorProduct.AlgebraTensorModule.curry_injective (LinearMap.ext_ring (LinearMap.ext fun v => ?_))
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_apply,
    TensorProduct.curry_apply, actOn_tmul, LinearMap.smul_apply, LinearMap.baseChange_tmul,
    hx, _root_.mul_one, TensorProduct.smul_tmul', smul_eq_mul]

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfLoc :
    TfAdm → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfLoc := by
  intro hAdm hAc hDec X M M' _ _ _ T L' Kw hF hAp t t' g
  set Φ : X → ℂ := fun y => T.tf (L'.loc t') (y⁻¹ * g) with hΦ
  have key : ∀ (a b : T.J), (a : M) = (b : M)⁻¹ → (((T.ψ a)⁻¹ : ℂˣ) : ℂ) = (T.ψ b : ℂ) := by
    intro a b hab
    have hab' : a = b⁻¹ := Subtype.ext (by simpa using hab)
    subst hab'
    simp
  have hTy : T.IsTy Φ := by
    intro k hk y
    have hp : T.L.pr (L'.loc t') = 1 := hAp.1 t'
    have h1 := ((hAdm X M T (L'.loc t') hp).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1
    simp only [hΦ, smul_eq_mul, mul_inv_rev, mul_assoc]
    rw [h1]
    congr 1
    exact key _ _ (by simp)
  have hsum := hAc X M M' T L' Kw hF hAp t 1 (by simp [TyLev.Cen]) ℂ Φ hTy 1
  have hL : conv T.K₀ (T.tf (L'.loc t)) (T.tf (L'.loc t')) g = hAct T.K₀ (T.tf (L'.loc t * 1)) Φ 1 := by
    simp only [conv, hAct, mul_one, one_mul, smul_eq_mul, hΦ]
  have hpt : ∀ m : M', Φ (L'.loc m) = T.tf 1 (g * (L'.loc (L'.pr g))⁻¹) * dosetInd ℂ Kw t' (m⁻¹ * L'.pr g) := by
    intro m
    have e1 : T.L.pr ((L'.loc m)⁻¹ * g) = T.L.pr g := by simp [hAp.1 m]
    have e2 : T.L.pr ((L'.loc (L'.pr g))⁻¹ * g) = T.L.pr g := by simp [hAp.1]
    have hu : g * (L'.loc (L'.pr g))⁻¹ = (L'.loc (L'.pr g))⁻¹ * g := by
      have h0 : L'.pr ((L'.loc (L'.pr g))⁻¹ * g) = 1 := by simp [L'.pr_loc]
      have hc := L'.comm (L'.pr g) _ h0
      calc g * (L'.loc (L'.pr g))⁻¹
          = (L'.loc (L'.pr g) * ((L'.loc (L'.pr g))⁻¹ * g)) * (L'.loc (L'.pr g))⁻¹ := by simp
        _ = (((L'.loc (L'.pr g))⁻¹ * g) * L'.loc (L'.pr g)) * (L'.loc (L'.pr g))⁻¹ := by rw [hc]
        _ = (L'.loc (L'.pr g))⁻¹ * g := by simp
    have hmem : (L'.loc m)⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t') (T.K : Set X) T.K ↔
        m⁻¹ * L'.pr g ∈ DoubleCoset.doubleCoset t' (Kw : Set M') Kw ∧
          (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset 1 (T.K : Set X) T.K := by
      have h3 : L'.pr ((L'.loc m)⁻¹ * g) = m⁻¹ * L'.pr g := by simp [L'.pr_loc]
      have h4 : (L'.loc (m⁻¹ * L'.pr g))⁻¹ * ((L'.loc m)⁻¹ * g) = (L'.loc (L'.pr g))⁻¹ * g := by
        simp [mul_assoc]
      have hd := hDec X M' L' T.K Kw hF t' 1 (map_one _) ((L'.loc m)⁻¹ * g)
      rw [mul_one, h3, h4] at hd
      exact hd
    simp only [hΦ, TyLev.tf]
    rw [hu, e1, e2]
    simp only [dosetInd, Set.indicator_apply, hmem, Pi.one_apply]
    by_cases ha : m⁻¹ * L'.pr g ∈ DoubleCoset.doubleCoset t' (Kw : Set M') Kw <;>
      by_cases hb : (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset 1 (T.K : Set X) T.K <;>
      simp [ha, hb]
  rw [hL, hsum]
  simp only [one_mul, smul_eq_mul, hpt, conv]
  rw [mul_finsum]
  congr 1
  ext x
  ring

import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem mul_mem_doubleCoset_iff_of_mem {X : Type} [Group X] (K : Subgroup X) (a g k : X) (hk : k ∈ K) :
    g * k ∈ DoubleCoset.doubleCoset a (K : Set X) K ↔ g ∈ DoubleCoset.doubleCoset a (K : Set X) K := by
  simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y * k⁻¹, K.mul_mem hy (K.inv_mem hk), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y * k, K.mul_mem hy hk, by rw [h, mul_assoc]⟩

private theorem loc_mem_doubleCoset_loc_iff {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X)
    (Kw : Subgroup M') (hF : L'.Fact K Kw) (t z : M') :
    L'.loc z ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K ↔
      z ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw := by
  simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    refine ⟨L'.pr x, hF.2 x hx, L'.pr y, hF.2 y hy, ?_⟩
    have h' := congrArg L'.pr h
    simpa [map_mul, L'.pr_loc] using h'
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨L'.loc x, hF.1 x hx, L'.loc y, hF.1 y hy, by rw [h, map_mul, map_mul]⟩

theorem UpperTheory.Gal.W2.Seed.pDosetCosets :
    ∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := by
  intro X M' _ _ L' K Kw hF t V _ _ Ψ hΨ
  set f : X ⧸ K → V := fun y => dosetInd ℂ K (L'.loc t) y.out • Ψ y.out with hf
  let φ : M' ⧸ Kw → X ⧸ K := fun x => ((L'.loc x.out : X) : X ⧸ K)
  have hφ : Function.Injective φ := by
    intro x x' h
    simp only [φ, QuotientGroup.eq] at h
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x', QuotientGroup.eq]
    have h2 := hF.2 _ h
    simpa [map_mul, map_inv, L'.pr_loc] using h2
  have hφf : ∀ x, f (φ x) = dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (L'.loc x.out)
    simp only [hf, φ, hk]
    rw [hΨ k k.2]
    simp only [dosetInd, Set.indicator, mul_mem_doubleCoset_iff_of_mem K _ _ _ k.2, loc_mem_doubleCoset_loc_iff L' K Kw hF,
      Pi.one_apply]
  have hsupp : Function.support f ⊆ Set.range φ := by
    intro y hy
    rw [Function.mem_support] at hy
    have hmem : y.out ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K := by
      by_contra hn
      apply hy
      simp [hf, dosetInd, hn]
    rw [DoubleCoset.mem_doubleCoset] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    refine ⟨((L'.pr a * t : M') : M' ⧸ Kw), ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Kw (L'.pr a * t)
    simp only [φ, hk]
    rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
    set n := a * (L'.loc (L'.pr a))⁻¹ with hn
    have hn1 : L'.pr n = 1 := by simp [hn, L'.pr_loc]
    have hnK : n ∈ K := K.mul_mem ha (K.inv_mem (hF.1 _ (hF.2 a ha)))
    have hy' : y.out = L'.loc (L'.pr a * t) * (n * b) := by
      calc y.out = a * L'.loc t * b := hab
        _ = n * L'.loc (L'.pr a * t) * b := by simp [hn, map_mul, mul_assoc]
        _ = L'.loc (L'.pr a * t) * n * b := by rw [L'.comm _ n hn1]
        _ = _ := mul_assoc _ _ _
    rw [hy', map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact K.mul_mem (K.inv_mem (hF.1 _ k.2)) (K.mul_mem hnK hb)
  calc ∑ᶠ y : X ⧸ K, f y = ∑ᶠ y ∈ Set.range φ, f y := by
        rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp]
    _ = ∑ᶠ x, f (φ x) := finsum_mem_range hφ
    _ = _ := finsum_congr hφf

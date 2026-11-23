import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.CoeffUnit

theorem mem_of_isIntegral_int {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h1 : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2

theorem isUnit_of_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l' : Level H) (c' : Coeff l') (W : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (A : Type) [CommRing A] (β : c'.V W →+* A), IsUnit (p : A) → ∀ a : c'.V W, a ≠ 0 → IsUnit (β a) := by
  intro E _ _ _ H l' c' W p hp hpW A _ β hpA a ha
  haveI := c'.fin

  set x : c'.F := (a : c'.F) with hxdef
  have hx0 : x ≠ 0 := by
    intro h; apply ha; exact Subtype.ext h
  have halg : IsAlgebraic ℤ (x⁻¹ : c'.F) := by
    have h1 : IsAlgebraic ℚ (x⁻¹ : c'.F) := Algebra.IsAlgebraic.isAlgebraic _
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ c'.F).mpr h1
  obtain ⟨d, hd0, hdint⟩ := halg.exists_integral_multiple

  obtain ⟨n, hn0, hnint⟩ : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : c'.F) * x⁻¹) := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · refine ⟨n, by exact_mod_cast hd0, ?_⟩
      rw [zsmul_eq_mul] at hdint; exact_mod_cast hdint
    · refine ⟨n, by simpa using hd0, ?_⟩
      have := hdint.neg
      rw [zsmul_eq_mul] at this
      convert this using 1; push_cast; ring
  obtain ⟨k, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one

  have hpmax : ((p : W)) ∈ IsLocalRing.maximalIdeal W := by
    obtain ⟨h1, h2⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hpW
    convert h2 using 1
    ext; simp
  have hmunit : IsUnit ((m : W)) := by
    by_contra hm
    have hmmax : ((m : W)) ∈ IsLocalRing.maximalIdeal W := hm
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
    have hbez : ((1 : ℤ)) = (p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m := by
      have := Nat.gcd_eq_gcd_ab p m
      rw [hcop] at this
      exact_mod_cast this
    have h1 : ((1 : W)) ∈ IsLocalRing.maximalIdeal W := by
      have : ((1 : W)) = (p : W) * (Nat.gcdA p m : W) + (m : W) * (Nat.gcdB p m : W) := by
        have := congrArg (fun t : ℤ => (t : W)) hbez
        push_cast at this
        exact this
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpmax) (Ideal.mul_mem_right _ _ hmmax)
    exact (IsLocalRing.maximalIdeal.isMaximal W).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨u, hu⟩ := hmunit

  have hnW : (((n : c'.F) * x⁻¹ : c'.F) : ℂ) ∈ W := by
    apply mem_of_isIntegral_int W
    exact hnint.map (c'.F.val.restrictScalars ℤ)
  have hum : (((u⁻¹ : Wˣ) : W) : ℂ) * (m : ℂ) = 1 := by
    have h1 : ((u⁻¹ : Wˣ) : W) * (m : W) = 1 := by rw [← hu]; exact u.inv_mul
    have h2 := congrArg (fun t : W => (t : ℂ)) h1
    simpa using h2
  have hinv : (((u⁻¹ : Wˣ) : W) : ℂ) = (m : ℂ)⁻¹ := eq_inv_of_mul_eq_one_left hum
  have hbW : ((((p : c'.F) ^ k * x⁻¹ : c'.F)) : ℂ) ∈ W := by
    have heq : ((((p : c'.F) ^ k * x⁻¹ : c'.F)) : ℂ)
        = (((u⁻¹ : Wˣ) : W) : ℂ) * ((((n : c'.F) * x⁻¹ : c'.F)) : ℂ) := by
      have hm0 : (m : ℂ) ≠ 0 := by
        have : m ≠ 0 := by rintro rfl; simp at hnm; exact hn0 hnm
        exact_mod_cast this
      rw [hinv, hnm]; push_cast; field_simp
    rw [heq]; exact W.mul_mem _ _ (SetLike.coe_mem _) hnW
  let b : c'.V W := ⟨(p : c'.F) ^ k * x⁻¹, ValuationSubring.mem_comap.mpr hbW⟩
  have hab : a * b = (p : c'.V W) ^ k := by
    apply Subtype.ext
    show (a : c'.F) * ((p : c'.F) ^ k * x⁻¹) = (((p : c'.V W) ^ k : c'.V W) : c'.F)
    rw [← hxdef]; push_cast; field_simp
  have hu' : IsUnit (β a * β b) := by
    rw [← map_mul, hab, map_pow, map_natCast]; exact hpA.pow k
  exact isUnit_of_mul_isUnit_left hu'

end GlobalTheory.CoeffUnit

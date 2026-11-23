import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

theorem eisensteinSum_scale_of_ne_zero (Λ : Submodule ℤ ℂ) {c : ℂ} (hc : c ≠ 0) (n : ℕ) :
    eisensteinSum (scaleLattice c Λ) n = (c ^ n)⁻¹ * eisensteinSum Λ n := by
  let e : Λ ≃ₗ[ℤ] scaleLattice c Λ :=
    Submodule.equivMapOfInjective (LinearMap.mulLeft ℤ c) (mul_right_injective₀ hc) Λ
  rw [eisensteinSum, eisensteinSum, ← e.toEquiv.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l ↦ ?_
  show ((c * (l : ℂ)) ^ n)⁻¹ = (c ^ n)⁻¹ * ((l : ℂ) ^ n)⁻¹
  rw [mul_pow, mul_inv]

theorem latticeDiscr_scale_of_ne_zero (Λ : Submodule ℤ ℂ) {c : ℂ} (hc : c ≠ 0) :
    latticeDiscr (scaleLattice c Λ) = (c ^ 12)⁻¹ * latticeDiscr Λ := by
  simp only [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_scale_of_ne_zero Λ hc]
  field_simp

variable {K : Type} [Field K] [NumberField K]

theorem idealLattice_spanSingleton_mul (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (x : K) :
    idealLattice σ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) * L.lattice =
      scaleLattice (σ x) L.lattice := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm l hl
    obtain ⟨y, hy, rfl⟩ := (mem_idealLattice σ).1 hm
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hy
    have hb : σ (algebraMap (𝓞 K) K b) ∈ latticeEnd L := by
      rw [hL]
      exact (mem_cmRing σ).2 ⟨b, rfl⟩
    refine Submodule.mem_map.2 ⟨σ (algebraMap (𝓞 K) K b) * l, hb l hl, ?_⟩
    simp only [LinearMap.mulLeft_apply, Algebra.smul_def, map_mul]
    ring
  · rw [scaleLattice, Submodule.map_le_iff_le_comap]
    intro l hl
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    exact Submodule.mul_mem_mul
      (map_mem_idealLattice σ (FractionalIdeal.mem_spanSingleton_self _ x)) hl

def spanNZ (a : 𝓞 K) (ha : a ≠ 0) : (Ideal (𝓞 K))⁰ :=
  ⟨Ideal.span {a}, mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.zero_eq_bot,
    Ideal.span_singleton_eq_bot])⟩

theorem discrRatio_span_singleton (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (a : 𝓞 K) (ha : a ≠ 0) :
    discrRatio σ L.lattice (FractionalIdeal.mk0 K (spanNZ a ha)) = σ (algebraMap (𝓞 K) K a) ^ 12 := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha
  have hσ : σ (algebraMap (𝓞 K) K a) ≠ 0 := (map_ne_zero σ).2 haK
  rw [discrRatio, Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0, spanNZ,
    FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv,
    idealLattice_spanSingleton_mul σ L hL, latticeDiscr_scale_of_ne_zero _ ((map_ne_zero σ).2 (inv_ne_zero haK)),
    map_inv₀, inv_pow, inv_inv, latticeDiscr_lattice, mul_div_assoc, div_self (discr_ne_zero L), mul_one]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg

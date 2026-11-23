import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PeriodLatticeIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

namespace WCocycle

theorem eisensteinSum_scaleLattice {c : ℂ} (hc : c ≠ 0) (N : Submodule ℤ ℂ) (n : ℕ) :
    eisensteinSum (scaleLattice c N) n = (c ^ n)⁻¹ * eisensteinSum N n := by
  have hinj : Function.Injective (LinearMap.mulLeft ℤ c) := fun x y h ↦
    mul_left_cancel₀ hc (by simpa using h)
  let e := Submodule.equivMapOfInjective (LinearMap.mulLeft ℤ c) hinj N
  rw [eisensteinSum, eisensteinSum, ← tsum_mul_left, scaleLattice, ← e.tsum_eq]
  congr 1
  ext x
  show ((c * (x : ℂ)) ^ n)⁻¹ = _
  rw [mul_pow, mul_inv]

theorem latticeDiscr_scaleLattice {c : ℂ} (hc : c ≠ 0) (N : Submodule ℤ ℂ) :
    latticeDiscr (scaleLattice c N) = (c ^ 12)⁻¹ * latticeDiscr N := by
  simp only [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_scaleLattice hc]
  field_simp

theorem mul_scaleLattice (c : ℂ) (M N : Submodule ℤ ℂ) :
    M * scaleLattice c N = scaleLattice c (M * N) := by
  apply le_antisymm
  · refine Submodule.mul_le.2 fun m hm n hn ↦ ?_
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hn
    refine Submodule.mem_map.2 ⟨m * y, Submodule.mul_mem_mul hm hy, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    ring
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.mul_le.2 fun m hm y hy ↦ ?_)
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply,
      show c * (m * y) = m * (c * y) by ring]
    exact Submodule.mul_mem_mul hm (Submodule.mem_map.2 ⟨y, hy, rfl⟩)

theorem latticeDiscr_idealLattice_mul_ne_zero (S : PrimeDiscriminant K) (σ : K →+* ℂ)
    (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    latticeDiscr (idealLattice σ ↑𝔟 * L.lattice) ≠ 0 := by
  have := S.isTotallyComplex
  have hK := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  obtain ⟨I, c, hc, hLI⟩ := exists_idealLattice_of_latticeEnd_eq σ hK L hL
  have hLc : L.lattice = scaleLattice c (idealLattice σ ↑I) := by
    apply SetLike.coe_injective
    rw [hLI, scaleLattice, Submodule.map_coe]
    rfl
  rw [hLc, mul_scaleLattice, latticeDiscr_scaleLattice hc, ← idealLattice_mul, ← Units.val_mul,
    ← lattice_idealPeriodPair σ hK, latticeDiscr_lattice]
  exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ hc)) (discr_ne_zero _)

theorem full (S : PrimeDiscriminant K) : WCocycle.Statement S := by
  intro σ L hL 𝔞 𝔭
  have hΛ : idealLattice σ ↑(𝔞 * 𝔭)⁻¹ * L.lattice =
      idealLattice σ ↑𝔭⁻¹ * (idealLattice σ ↑𝔞⁻¹ * L.lattice) := by
    rw [mul_inv, Units.val_mul, idealLattice_mul, mul_comm (idealLattice σ ↑𝔞⁻¹), mul_assoc]
  have h0 : latticeDiscr L.lattice ≠ 0 := by
    rw [latticeDiscr_lattice]; exact discr_ne_zero L
  have h1 := latticeDiscr_idealLattice_mul_ne_zero S σ L hL 𝔞⁻¹
  simp only [discrRatio, hΛ]
  field_simp

end WCocycle

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg

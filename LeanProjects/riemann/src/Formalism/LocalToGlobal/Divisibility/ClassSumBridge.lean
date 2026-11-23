import Formalism.LocalToGlobal.Divisibility.ClassSumLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV.CSD

open Formalism.DivisionValues

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)

def pairOne (K : Type) [Field K] [StarRing K] : K →ₗ⋆[K] K →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
    (by intro x y z; simp [add_mul]) (by intro a x y; simp [mul_assoc, starRingEnd_apply])
    (by intro x y z; simp [mul_add]) (by intro a x y; simp [mul_left_comm])

def one (K : Type) [Field K] [NumberField K] [StarRing K] : CSD K where
  Cl := Unit
  V := K
  ιV := Unit
  bV := Basis.singleton Unit K
  pair := pairOne K
  Gam := fun _ => Unit
  grpGam := fun _ => inferInstance
  ρ := fun _ => 1
  Nab := fun _ => 1
  Del := fun _ => 1

theorem pairOne_apply (K : Type) [Field K] [StarRing K] (x y : K) : pairOne K x y = star x * y := rfl

theorem star_mem_one {K : Type} [Field K] [NumberField K] [StarRing K] {z : K}
    (hz : z ∈ (1 : Submodule (𝓞 K) K)) : star z ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hz
  exact Submodule.mem_one.mpr ⟨cO K a, rfl⟩

theorem mem_dual_one {K : Type} [Field K] [NumberField K] [StarRing K] (y : K) :
    y ∈ Formalism.HermitianLatticesTheory.dual (pairOne K) (1 : Submodule (𝓞 K) K) ↔ y ∈ (1 : Submodule (𝓞 K) K) := by
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars, pairOne_apply]
  constructor
  · intro h
    simpa using h 1 (Submodule.one_le.mp le_rfl)
  · intro hy z hz
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (star_mem_one hz)
    obtain ⟨b, hb⟩ := Submodule.mem_one.mp hy
    exact Submodule.mem_one.mpr ⟨a * b, by rw [map_mul, ha, hb]⟩

theorem one_good (K : Type) [Field K] [NumberField K] [StarRing K] : (one K).Good 1 where
  symm := by
    refine ⟨fun (x y : K) => ?_⟩
    show starRingEnd K (star x * y) = star y * x
    rw [starRingEnd_apply, star_mul', star_star, mul_comm]
  nondeg := by
    constructor
    · intro (x : K) hx
      have h1 : star x * (1 : K) = 0 := hx (1 : K)
      have h2 : x = (0 : K) := by simpa using h1
      exact h2
    · intro (y : K) hy
      have h1 : star (1 : K) * y = 0 := hy (1 : K)
      have h2 : y = (0 : K) := by simpa using h1
      exact h2
  inv := by intro c γ x y; rfl
  nab_lat := by
    intro c
    show Submodule.IsLattice K (1 : Submodule (𝓞 K) K)
    refine ⟨by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _, ?_⟩
    rw [eq_top_iff]
    intro x _
    have : x = x • (1 : K) := by simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.one_le.mp le_rfl))
  del_le := fun _ => le_rfl
  del_stable := by intro c γ y hy; exact hy
  s_pos := Nat.one_pos
  dual_le := by
    intro c (y : K) hy
    have h1 : y ∈ (1 : Submodule (𝓞 K) K) := (mem_dual_one y).mp hy
    exact Submodule.smul_mem _ _ h1
  del_dual := by
    intro c (y : K) hy
    have h1 : y ∈ Formalism.HermitianLatticesTheory.dual (pairOne K) (1 : Submodule (𝓞 K) K) := (mem_dual_one y).mpr hy
    exact Submodule.smul_mem _ _ h1

end Formalism.L2.DIV.CSD

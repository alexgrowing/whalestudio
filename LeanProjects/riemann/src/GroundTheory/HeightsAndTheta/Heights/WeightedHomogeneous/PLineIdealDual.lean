import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsPointHeight
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.LinearFormEqZeroOfIntegers
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace LineIdealDual

theorem algebraMap_mem_range_ringOfIntegers {K K' : Type*} [Field K] [Field K'] [Algebra K K'] (y : 𝓞 K) :
    algebraMap K K' (algebraMap (𝓞 K) K y) ∈ Set.range (algebraMap (𝓞 K') K') :=
  ⟨RingOfIntegers.mapRingHom (algebraMap K K') y, rfl⟩

theorem latticeValue_smul {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {m N : ℕ}
    (φ : Fin (N + 1) → Fin m → K) (a : K') (v : Fin m → K') (b : Fin (N + 1)) :
    latticeValue φ (a • v) b = a * latticeValue φ v b := by
  simp only [latticeValue, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

theorem latticeValue_algebraMap {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {m N : ℕ}
    (φ : Fin (N + 1) → Fin m → K) (w : Fin m → K) (b : Fin (N + 1)) :
    latticeValue φ (fun j ↦ algebraMap K K' (w j)) b = algebraMap K K' (φ b ⬝ᵥ w) := by
  simp [latticeValue, dotProduct, map_sum, map_mul]

theorem proof : LineIdealDual.Statement := by
  intro K _ _ r N F φ hφ K' _ _ _ v a
  classical
  have hdual : ∀ ψ ∈ Submodule.span ℤ (Set.range φ), ψ ∈ latticeDual F.lattice := by
    intro ψ hψ
    rw [hφ.span_eq] at hψ
    exact hψ
  constructor
  · intro hv b
    let Φ : (Fin (r + 1) → K') →ₗ[𝓞 K'] K' :=
      { toFun := fun x ↦ latticeValue φ x b
        map_add' := fun x y ↦ by
          simp only [latticeValue, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := fun c x ↦ by
          simp only [latticeValue, Pi.smul_apply, Algebra.smul_def, RingHom.id_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring }
    have hle : latticeExtend K' F.lattice ≤ (1 : Submodule (𝓞 K') K').comap Φ := by
      rw [latticeExtend, Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨y, hy⟩ := hdual (φ b) (Submodule.subset_span ⟨b, rfl⟩) w hw
      change latticeValue φ (fun j ↦ algebraMap K K' (w j)) b ∈ (1 : Submodule (𝓞 K') K')
      rw [latticeValue_algebraMap, ← hy, Submodule.mem_one]
      exact algebraMap_mem_range_ringOfIntegers y
    have h1 : latticeValue φ (a • v) b ∈ (1 : Submodule (𝓞 K') K') := hle hv
    rw [latticeValue_smul, Submodule.mem_one] at h1
    exact h1
  · intro h
    obtain ⟨n, f, σ, hfF, hσF, hid⟩ :=
      GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf.exists_dualBasis F.lattice F.fg

    have hgex : ∀ i, ∃ gi : Fin (r + 1) → K, ∀ w, σ i w = gi ⬝ᵥ w := fun i ↦
      ⟨fun j ↦ σ i (fun l ↦ if j = l then 1 else 0), fun w ↦ by
        rw [LinearMap.pi_apply_eq_sum_univ (σ i) w]
        simp [dotProduct, mul_comm]⟩
    choose g hg using hgex

    have hgmem : ∀ i, g i ∈ Submodule.span ℤ (Set.range φ) := by
      intro i
      rw [hφ.span_eq]
      intro w hw
      rw [← hg]
      exact hσF i w hw
    choose c hc using fun i ↦ (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hgmem i)

    have hKid : ∀ j k : Fin (r + 1), ∑ i, g i j * f i k = if j = k then 1 else 0 := by
      intro j k
      have hmem : (fun l : Fin (r + 1) ↦ if j = l then (1 : K) else 0) ∈
          Submodule.span K (F.lattice : Set (Fin (r + 1) → K)) := by
        rw [F.span_eq]
        exact Submodule.mem_top
      have := congrFun (hid _ hmem) k
      simpa [Finset.sum_apply, hg, dotProduct] using this.symm

    have hid' : ∀ x : Fin (r + 1) → K',
        x = ∑ i, (∑ j, algebraMap K K' (g i j) * x j) • fun k ↦ algebraMap K K' (f i k) := by
      intro x
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      have e : ∀ j, ∑ i, algebraMap K K' (g i j) * x j * algebraMap K K' (f i k) =
          x j * algebraMap K K' (if j = k then 1 else 0) := by
        intro j
        rw [← hKid j k, map_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [map_mul]; ring
      simp only [e, apply_ite (algebraMap K K'), map_one, map_zero, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    choose y hy using h
    rw [hid' (a • v)]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hcoef : ∑ j, algebraMap K K' (g i j) * (a • v) j =
        algebraMap (𝓞 K') K' (∑ b, (c i b : 𝓞 K') * y b) := by
      rw [← hc i]
      simp only [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul, map_sum, map_mul, map_intCast, hy,
        latticeValue, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun j _ ↦ by
        simp only [Pi.mul_apply, Pi.intCast_apply, map_mul, map_intCast]; ring
    rw [hcoef, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f i, hfF i, rfl⟩)

end LineIdealDual

end

end GroundTheory.Heights₂.Heights

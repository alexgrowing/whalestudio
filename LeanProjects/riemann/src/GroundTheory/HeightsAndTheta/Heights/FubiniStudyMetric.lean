import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FubiniStudyCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ContDiff
open Topology Set

noncomputable section

variable {N : ℕ}

def normSq2 {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

def norm2 {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := √(normSq2 v)

section Norm2

variable {ι : Type*} [Fintype ι]

lemma normSq2_nonneg (v : ι → ℂ) : 0 ≤ normSq2 v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma normSq2_pos {v : ι → ℂ} (hv : v ≠ 0) : 0 < normSq2 v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩

lemma euclideanNorm_pos {v : ι → ℂ} (hv : v ≠ 0) : 0 < norm2 v := Real.sqrt_pos.mpr (normSq2_pos hv)

lemma euclideanNorm_sq (v : ι → ℂ) : norm2 v ^ 2 = normSq2 v := Real.sq_sqrt (normSq2_nonneg v)

lemma normSq2_smul (t : ℂ) (v : ι → ℂ) : normSq2 (t • v) = ‖t‖ ^ 2 * normSq2 v := by
  simp [normSq2, mul_pow, Finset.mul_sum]

lemma euclideanNorm_smul (t : ℂ) (v : ι → ℂ) : norm2 (t • v) = ‖t‖ * norm2 v := by
  rw [norm2, normSq2_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]; rfl

lemma norm_le_norm2 (v : ι → ℂ) (i : ι) : ‖v i‖ ≤ norm2 v := by
  rw [norm2]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖v j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

end Norm2

namespace CP

lemma normSq2_chartVec (i : Fin (N + 1)) (z : Fin N → ℂ) :
    normSq2 (chartVec i z) = 1 + ∑ j, ‖z j‖ ^ 2 := by
  rw [normSq2, Fin.sum_univ_succAbove _ i]
  simp

def tautLine (x : CP N) : Submodule ℂ (Fin (N + 1) → ℂ) := x.submodule

lemma rep_mem_tautLine (x : CP N) : x.rep ∈ tautLine x := by
  rw [tautLine, Projectivization.submodule_eq]; exact Submodule.mem_span_singleton_self _

lemma mem_tautLine_mk (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) : v ∈ tautLine (Projectivization.mk ℂ v hv) := by
  rw [tautLine, Projectivization.submodule_mk]; exact Submodule.mem_span_singleton_self _

abbrev O1 (x : CP N) : Type := Module.Dual ℂ (tautLine x)

def fsNorm (x : CP N) (φ : O1 x) : ℝ := ‖φ ⟨x.rep, rep_mem_tautLine x⟩‖ / norm2 x.rep

theorem fsNorm_eq (x : CP N) (φ : O1 x) (v : Fin (N + 1) → ℂ) (hv : v ∈ tautLine x) (hv0 : v ≠ 0) :
    fsNorm x φ = ‖φ ⟨v, hv⟩‖ / norm2 v := by
  have hv' := hv
  rw [tautLine, Projectivization.submodule_eq, Submodule.mem_span_singleton] at hv'
  obtain ⟨t, rfl⟩ := hv'
  have ht : t ≠ 0 := by rintro rfl; simp at hv0
  have : (⟨t • x.rep, hv⟩ : tautLine x) = t • ⟨x.rep, rep_mem_tautLine x⟩ := rfl
  rw [this, map_smul, smul_eq_mul, norm_mul, euclideanNorm_smul, fsNorm]
  have hn : 0 < norm2 x.rep := euclideanNorm_pos x.rep_nonzero
  have ht' : 0 < ‖t‖ := norm_pos_iff.mpr ht
  field_simp

lemma tautologicalDual_ext (x : CP N) {φ ψ : O1 x} (h : φ ⟨x.rep, rep_mem_tautLine x⟩ = ψ ⟨x.rep, rep_mem_tautLine x⟩) :
    φ = ψ := by
  ext ⟨w, hw⟩
  have hw' := hw
  rw [tautLine, Projectivization.submodule_eq, Submodule.mem_span_singleton] at hw'
  obtain ⟨t, rfl⟩ := hw'
  have : (⟨t • x.rep, hw⟩ : tautLine x) = t • ⟨x.rep, rep_mem_tautLine x⟩ := rfl
  rw [this, map_smul, map_smul, h]

theorem fsNorm_eq_zero_iff (x : CP N) (φ : O1 x) : fsNorm x φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    have hn : 0 < norm2 x.rep := euclideanNorm_pos x.rep_nonzero
    rw [fsNorm, div_eq_zero_iff, norm_eq_zero] at h
    rcases h with h | h
    · exact tautologicalDual_ext x (by simpa using h)
    · exact absurd h hn.ne'
  · rintro rfl; simp [fsNorm]

def restrictForm (ℓ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ) (x : CP N) : O1 x := ℓ.domRestrict (tautLine x)

theorem fsNorm_restrictForm_mk (ℓ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    fsNorm (Projectivization.mk ℂ v hv) (restrictForm ℓ _) = ‖ℓ v‖ / norm2 v :=
  fsNorm_eq _ _ v (mem_tautLine_mk v hv) hv

def coordForm (i : Fin (N + 1)) : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj i

theorem restrictForm_coordForm_ne_zero (i : Fin (N + 1)) {x : CP N} (hx : x ∈ chartDomain i) :
    restrictForm (coordForm i) x ≠ 0 := by
  induction x using Projectivization.ind with
  | h v hv =>
    intro h
    have := (fsNorm_eq_zero_iff _ _).mpr h
    rw [fsNorm_restrictForm_mk, div_eq_zero_iff, norm_eq_zero] at this
    rcases this with h1 | h1
    · exact hx h1
    · exact (euclideanNorm_pos hv).ne' h1

theorem fsNorm_sq_chartInv (ℓ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ) (i : Fin (N + 1)) (z : Fin N → ℂ) :
    fsNorm (chartInv i z) (restrictForm ℓ _) ^ 2 = ‖ℓ (chartVec i z)‖ ^ 2 / (1 + ∑ j, ‖z j‖ ^ 2) := by
  rw [chartInv, fsNorm_restrictForm_mk, div_pow, euclideanNorm_sq, normSq2_chartVec]

theorem fsNorm_sq_frame (i : Fin (N + 1)) (z : Fin N → ℂ) :
    fsNorm (chartInv i z) (restrictForm (coordForm i) _) ^ 2 = 1 / (1 + ∑ j, ‖z j‖ ^ 2) := by
  rw [fsNorm_sq_chartInv]
  simp [coordForm]

lemma contDiff_normSqSum : ContDiff ℝ ∞ (fun z : Fin N → ℂ => ∑ j, ‖z j‖ ^ 2) :=
  ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ j)

end CP

end

end GroundTheory.Heights₂.Heights

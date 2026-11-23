import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.ConjUnitary
open Matrix

theorem unitary_of_norm_preserving {N : ℕ} (V : Matrix (Fin N) (Fin N) ℂ)
    (h : ∀ z : Fin N → ℂ, ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    V ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hn : ∀ v : EuclideanSpace ℂ (Fin N), ‖toEuclideanCLM (n := Fin N) (𝕜 := ℂ) V v‖ = ‖v‖ := by
    intro v
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simpa using h v.ofLp
  have h1 := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 hn
  rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← ContinuousLinearMap.mul_def, ← map_mul,
    ← map_one (toEuclideanCLM (n := Fin N) (𝕜 := ℂ))] at h1
  rw [Matrix.mem_unitaryGroup_iff']
  exact (toEuclideanCLM (n := Fin N) (𝕜 := ℂ)).injective h1

theorem conj_mulVec {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (z : Fin N → ℂ) :
    (fun j => (starRingEnd ℂ) ((M *ᵥ fun k => (starRingEnd ℂ) (z k)) j)) =
      M.map (starRingEnd ℂ) *ᵥ z := by
  ext j
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem conj_frame_unitary : ∀ (K : Type) [Field K] (N : ℕ) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), GlobalTheory.ChowHt.ConjCompat A → (∀ σ, (A σ).det ≠ 0) →
    ∀ σ : K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U := by
  intro K _ N A hC hdet σ
  set B := A ((starRingEnd ℂ).comp σ) with hBdef
  set A0 := A σ with hA0
  set C := A0.map (starRingEnd ℂ) with hCdef
  set V := B⁻¹ * C with hV
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.2 (hdet _)
  have hA0u : IsUnit A0.det := isUnit_iff_ne_zero.2 (hdet _)
  have hnorm : ∀ z : Fin N → ℂ, ∑ i, ‖(V *ᵥ z) i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    intro z
    have h := hC σ (A0 *ᵥ fun k => (starRingEnd ℂ) (z k))
    rw [← hBdef, ← hA0, conj_mulVec] at h
    unfold GlobalTheory.ChowHt.frameNorm at h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA0u,
      Matrix.one_mulVec, ← hV] at h
    rw [Real.sqrt_inj (Finset.sum_nonneg fun _ _ => by positivity)
      (Finset.sum_nonneg fun _ _ => by positivity)] at h
    rw [h]
    simp
  have hVu := unitary_of_norm_preserving V hnorm
  refine ⟨star V, Unitary.star_mem hVu, ?_⟩
  have hVs : V * star V = 1 := (Matrix.mem_unitaryGroup_iff).1 hVu
  have hBV : B * V = C := by
    rw [hV, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul]
  rw [← hBV, Matrix.mul_assoc, hVs, Matrix.mul_one]

end GlobalTheory.ConjUnitary

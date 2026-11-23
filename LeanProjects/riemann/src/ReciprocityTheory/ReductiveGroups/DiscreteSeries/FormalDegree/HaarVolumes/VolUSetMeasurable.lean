import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUMeasurableSetTriPos

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

theorem volU_real {V η ε a b e i : ℝ} (hV : 0 < V) (he : 0 < e) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) (hkey : (1 - ε) * (1 + η) = 1 + ε)
    (h1 : V * (i * a) ≤ (1 + ε) * (b * e)) (h2 : (1 - ε) * (b * e) ≤ V * (i * a))
    (h3 : (1 - ε) * e ≤ i) (h4 : i ≤ (1 + ε) * e) :
    a ≤ (1 + η) / V * b ∧ (1 - η) / V * b ≤ a := by
  have hε' : 0 < 1 - ε := by linarith
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hV]
    have k1 : V * a * ((1 - ε) * e) ≤ V * a * i :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hV.le ha)
    have k2 : (1 + ε) * (b * e) = (1 - ε) * (1 + η) * (b * e) := by rw [hkey]
    have k3 : (1 - ε) * e * (a * V) ≤ (1 - ε) * e * ((1 + η) * b) := by
      linarith [k1, h1, k2]
    exact le_of_mul_le_mul_left k3 (mul_pos hε' he)
  · rw [div_mul_eq_mul_div, div_le_iff₀ hV]
    have k1 : V * a * i ≤ V * a * ((1 + ε) * e) :=
      mul_le_mul_of_nonneg_left h4 (mul_nonneg hV.le ha)
    have k2 : (1 + ε) * (1 - η) * (b * e) = (1 - ε) * (1 + η) * (1 - η) * (b * e) := by
      rw [hkey]
    have k3 : 0 ≤ (1 - ε) * η ^ 2 * (b * e) :=
      mul_nonneg (mul_nonneg hε'.le (sq_nonneg η)) (mul_nonneg hb he.le)
    have k4 : (1 + ε) * e * ((1 - η) * b) ≤ (1 + ε) * e * (a * V) := by
      linarith [k1, h2, k2, k3]
    exact le_of_mul_le_mul_left k4 (mul_pos (by linarith) he)

def volUSet (B : Set (UCo N)) : Set (UNgrp N) := {k | ∃ x ∈ B, toM k = NormedSpace.exp (skMat x)}

theorem volUSet_measurable {δ : ℝ}
    (hinj : Set.InjOn (fun x : UCo N => NormedSpace.exp (skMat x)) (Metric.ball 0 δ))
    {B : Set (UCo N)} (hB : MeasurableSet B) (hBs : B ⊆ Metric.ball 0 δ) :
    MeasurableSet (volUSet B) := by
  set F : UCo N → (Fin N → Fin N → ℂ) := fun x => Matrix.of.symm (NormedSpace.exp (skMat x)) with hF
  set G : UNgrp N → (Fin N → Fin N → ℂ) := fun k => Matrix.of.symm (toM k) with hG
  have hS : volUSet B = G ⁻¹' (F '' B) := by
    ext k
    simp only [volUSet, Set.mem_preimage, Set.mem_image, hF, hG]
    constructor
    · rintro ⟨x, hx, hk⟩
      exact ⟨x, hx, by rw [hk]⟩
    · rintro ⟨x, hx, hk⟩
      exact ⟨x, hx, (Matrix.of.symm.injective hk).symm⟩
  have hGc : Continuous G := continuous_toM _
  have hexp : Continuous (fun X : Matrix (Fin N) (Fin N) ℂ => NormedSpace.exp X) := by
    let _ : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℚ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
    exact @NormedSpace.exp_continuous (Matrix (Fin N) (Fin N) ℂ) _ _
      (inferInstanceAs (CompleteSpace (Fin N → Fin N → ℂ)))
  have hFc : Continuous F := hexp.comp volU_continuous_skMat
  rw [hS]
  refine hGc.measurable ?_
  refine MeasurableSet.image_of_continuousOn_injOn hB hFc.continuousOn ?_
  intro x hx y hy hxy
  exact hinj (hBs hx) (hBs hy) (Matrix.of.symm.injective hxy)

theorem volU_image_eq (B : Set (UCo N)) (ρ : ℝ) :
    chartWR '' (B ×ˢ Metric.ball 0 ρ) = qrMap '' (volUSet B ×ˢ Metric.ball (volUOne N) ρ) := by
  ext Z
  constructor
  · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have hmem : NormedSpace.exp (skMat x) ∈ Set.range (fun g : UNgrp N => toM g) := by
      rw [range_toM]
      exact volU_exp_inUJ x
    obtain ⟨k, hk⟩ := hmem
    have hk' : toM k = NormedSpace.exp (skMat x) := hk
    refine ⟨(k, t + volUOne N), ⟨⟨x, hx, hk'⟩, ?_⟩, ?_⟩
    · show dist (t + volUOne N) (volUOne N) < ρ
      rw [dist_eq_norm, add_sub_cancel_right, ← dist_zero_right]
      exact ht
    · simp only [qrMap, chartWR, volU_upMat_add, hk']
  · rintro ⟨⟨k, t⟩, ⟨⟨x, hx, hk⟩, ht⟩, rfl⟩
    refine ⟨(x, t - volUOne N), ⟨hx, ?_⟩, ?_⟩
    · show dist (t - volUOne N) 0 < ρ
      rw [dist_zero_right, ← dist_eq_norm]
      exact ht
    · have ht' : upMat t = 1 + upMat (t - volUOne N) := by
        rw [← volU_upMat_add, sub_add_cancel]
      have hk' : toM k = NormedSpace.exp (skMat x) := hk
      simp only [qrMap, chartWR, ht']
      rw [hk']

end ReciprocityTheory.ChartRestriction.DS

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsDiagR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem mem_mcPts_span_singleton {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {s : MRing ι} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (hs : eval z (map (Int.castRingHom ℂ) s) = 0) : z ∈ mcPts (Ideal.span {s}) := by
  refine ⟨hz.1, fun f hf => ?_⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  rw [map_mul, map_mul, hs, mul_zero]

theorem ZeroSetNull.proof : ZeroSetNull.Statement := by
  intro K _ ι _ P e s a φ g₁ g₂ hP hs hsP hg
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ
  · rw [dif_pos hΨ, dif_pos hΨ]
    set Ψ := hΨ.choose with hΨdef
    have hJ : IsMultiHomogIdeal (Ideal.span {s}) :=
      ⟨{s}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hs⟩, rfl⟩
    have hJP : ¬ Ideal.span {s} ≤ P := fun h => hsP (h (Ideal.subset_span rfl))
    have hnull := projB_null Ψ hP hΨ.choose_spec hJ hJP
    unfold ptsIntegralAt
    refine integral_congr_ae ?_
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun y hy => ?_) hnull
    by_contra hyB
    apply hy
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · rw [dif_pos hγ, dif_pos hγ]
      obtain ⟨-, hev⟩ := hγ.choose_spec
      obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
      have hs0 : eval (hγ.choose y) (map (Int.castRingHom ℂ) s) ≠ 0 := fun h0 =>
        hyB ⟨hγ.choose y, hmem, mem_mcPts_span_singleton hmem h0, hproj⟩
      rw [hg _ hmem hs0]
    · rw [dif_neg hγ, dif_neg hγ]
  · rw [dif_neg hΨ, dif_neg hΨ]

end GroundTheory.Heights₂.Heights.Inter

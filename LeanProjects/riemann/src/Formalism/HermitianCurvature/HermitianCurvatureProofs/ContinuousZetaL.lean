import Formalism.HermitianCurvature.HermitianCurvatureProofs.MrelConjTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k ρ : ℕ}

theorem glev_last_eq (r : ℕ) : Glev k r (Fin.last r) = B2.UWb k r := by
  ext g
  simp only [Glev, B2.UWb, Fin.val_last]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a => h2 a a.isLt⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a _ => h2 a⟩

theorem image_glev : ιLev k 1 ρ '' Glev k ρ (Fin.last ρ) = Glev k (1 + ρ) (Fin.last (1 + ρ)) := by
  rw [glev_last_eq, glev_last_eq, Formalism.FourierDecayAlt.P.LongWeylElement.uWbRec k ρ]

theorem map_levM_smul {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hμ : B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs) :
    ∃ c : NNReal, μs.map (B2.levM k ρ) = c • μ := by
  rw [glev_last_eq] at hμs hμ
  have hU := Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k ρ
  obtain ⟨_, hν⟩ := Formalism.FourierDecayAlt.P.levi_haar_measure_exists k ρ _ μs hU hμs
  have e : ιLev k 1 ρ '' B2.UWb k ρ = B2.UWb k (1 + ρ) := by
    rw [← glev_last_eq, ← glev_last_eq, image_glev]
  rw [e] at hν
  exact Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k (1 + ρ) _ μ _ (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k (1 + ρ)) hμ hν.conc
    hν.left hν.finite_compact

theorem zeta_levM (z z' : Fin (2 * ρ + k + 1) → ℂ) (x : Mt k ρ) :
    zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of (B2.levM k ρ x)) =
      zetaL k ρ z z' (Fin.last ρ) (Matrix.of x) := by
  have hf : ∀ (r : ℕ) (v : Fin (2 * r + k + 1) → ℂ), fvec k r v (Fin.last r) = v := fun r v => by
    simp [fvec]
  change herm (Hpk k (1 + ρ)) (ιLev k 1 ρ (Matrix.of x) *ᵥ fvec k (1 + ρ) (liftVec k 1 ρ z') (Fin.last (1 + ρ)))
      (fvec k (1 + ρ) (liftVec k 1 ρ z) (Fin.last (1 + ρ))) =
    herm (Hpk k ρ) (Matrix.of x *ᵥ fvec k ρ z' (Fin.last ρ)) (fvec k ρ z (Fin.last ρ))
  rw [hf, hf, hf, hf, Formalism.FourierDecayAlt.P.B2x5.lev_lift, Formalism.FourierDecayAlt.P.B2x4.herm_lift]

theorem measurable_levM : Measurable (B2.levM k ρ) := by
  exact (Formalism.FourierDecayAlt.P.LongWeylElement.levM_cont k ρ).measurable

theorem continuous_zetaL (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun x : Mt k r => zetaL k r z z' (Fin.last r) (Matrix.of x) := by
  exact (LinearMap.continuous_of_finiteDimensional (Formalism.FourierDecayAlt.P.Qx5.zetaLin k r z z' (Fin.last r))).comp continuous_id

theorem map_levM_eq {z z' : Fin (2 * ρ + k + 1) → ℂ} {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hμ : B.IsHaarOn (Glev k (1 + ρ) (Fin.last (1 + ρ))) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (wt : ℂ → ℝ≥0∞) (hfin : ∀ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ < (⊤ : ℝ≥0∞))
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, wt ζ * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ z z' (Fin.last ρ) (Matrix.of x)) ∂μs = ∫⁻ ζ, wt ζ * ψ ζ) :
    μs.map (B2.levM k ρ) = μ := by
  obtain ⟨c, hc⟩ := map_levM_smul hμ hμs
  have key : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ → c • ∫⁻ ζ, wt ζ * ψ ζ = ∫⁻ ζ, wt ζ * ψ ζ := by
    intro ψ hψ
    have hm : Measurable fun y : Mt k (1 + ρ) =>
        ψ (zetaL k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') (Fin.last (1 + ρ)) (Matrix.of y)) :=
      hψ.comp (continuous_zetaL (1 + ρ) _ _).measurable
    rw [← hlaw ψ hψ, ← lintegral_smul_measure, ← hc, lintegral_map hm measurable_levM]
    simp_rw [zeta_levM]
    rw [hlaws ψ hψ, hlaw ψ hψ]
  by_cases hR : ∃ R : ℝ, ∫⁻ ζ in Metric.closedBall 0 R, wt ζ ≠ 0
  · obtain ⟨R, hR⟩ := hR
    have hψ : Measurable ((Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞)) :=
      measurable_one.indicator Metric.isClosed_closedBall.measurableSet
    have h1 := key _ hψ
    have e : ∫⁻ ζ, wt ζ * (Metric.closedBall (0 : ℂ) R).indicator (1 : ℂ → ℝ≥0∞) ζ =
        ∫⁻ ζ in Metric.closedBall 0 R, wt ζ := by
      rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
      congr 1
      funext ζ
      by_cases hζ : ζ ∈ Metric.closedBall (0 : ℂ) R <;> simp [hζ]
    rw [e, ENNReal.smul_def] at h1
    have h2 : (c : ℝ≥0∞) * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ = 1 * ∫⁻ ζ in Metric.closedBall 0 R, wt ζ := by
      rw [one_mul]
      exact h1
    have hc1 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hR (hfin R).ne).mp h2
    rw [hc, ENNReal.coe_eq_one.mp hc1, one_smul]
  · push_neg at hR
    have h0 : ∫⁻ ζ, wt ζ = 0 := by
      rw [← setLIntegral_univ, ← Metric.iUnion_closedBall_nat (0 : ℂ)]
      refine le_antisymm ((lintegral_iUnion_le _ _).trans ?_) zero_le'
      simp [hR]
    have hμ0 : μ = 0 := by
      have h3 := hlaw (fun _ => 1) measurable_const
      simp only [mul_one, h0, lintegral_const, one_mul] at h3
      exact Measure.measure_univ_eq_zero.mp h3
    have hμs0 : μs = 0 := by
      have h3 := hlaws (fun _ => 1) measurable_const
      simp only [mul_one, h0, lintegral_const, one_mul] at h3
      exact Measure.measure_univ_eq_zero.mp h3
    rw [hμ0, hμs0, Measure.map_zero]

end Formalism.FourierDecayAlt.P.PBH

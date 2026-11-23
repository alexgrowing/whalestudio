import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnFundamentalDomain
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLeftInvariantOfIsAutForm

noncomputable section

open NumberField MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.Rs.JExpNegGlue

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [T2Space G]

def Dec (μ : Measure G) (ρ : ℝ) (a : ℝ → G) (H : G → ℂ) : Prop :=
  Continuous H ∧ ∀ Q : Set G, IsCompact Q →
    Tendsto (fun t : ℝ => Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖H (a t * g)‖ ^ 2 ∂μ) atTop (𝓝 0)

variable (μ : Measure G) [μ.IsHaarMeasure] (ρ : ℝ) (a : ℝ → G)

theorem intOn {H : G → ℂ} (hH : Continuous H) {Q : Set G} (hQ : IsCompact Q) (t : ℝ) :
    IntegrableOn (fun g => ‖H (a t * g)‖ ^ 2) Q μ :=
  ((hH.comp (continuous_const.mul continuous_id)).norm.pow 2).continuousOn.integrableOn_compact hQ

theorem dec_zero : Dec μ ρ a 0 := by
  refine ⟨continuous_const, fun Q _ => ?_⟩
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))

theorem dec_add {H₁ H₂ : G → ℂ} (h₁ : Dec μ ρ a H₁) (h₂ : Dec μ ρ a H₂) : Dec μ ρ a (H₁ + H₂) := by
  refine ⟨h₁.1.add h₂.1, fun Q hQ => ?_⟩
  have hlim := ((h₁.2 Q hQ).const_mul 2).add ((h₂.2 Q hQ).const_mul 2)
  simp only [mul_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun t => ?_) (fun t => ?_)
  · exact mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => by positivity)
  · have hle : ∫ g in Q, ‖(H₁ + H₂) (a t * g)‖ ^ 2 ∂μ ≤
        ∫ g in Q, (2 * ‖H₁ (a t * g)‖ ^ 2 + 2 * ‖H₂ (a t * g)‖ ^ 2) ∂μ := by
      refine integral_mono (intOn μ a (h₁.1.add h₂.1) hQ t)
        (((intOn μ a h₁.1 hQ t).const_mul 2).add ((intOn μ a h₂.1 hQ t).const_mul 2)) (fun g => ?_)
      simp only [Pi.add_apply]
      have h := norm_add_le (H₁ (a t * g)) (H₂ (a t * g))
      have h' := mul_le_mul h h (norm_nonneg _) (by positivity)
      nlinarith [sq_nonneg (‖H₁ (a t * g)‖ - ‖H₂ (a t * g)‖)]
    rw [integral_add ((intOn μ a h₁.1 hQ t).const_mul 2) ((intOn μ a h₂.1 hQ t).const_mul 2),
      integral_const_mul, integral_const_mul] at hle
    have he := (Real.exp_pos (-(2 * ρ * t))).le
    calc _ ≤ Real.exp (-(2 * ρ * t)) * (2 * ∫ g in Q, ‖H₁ (a t * g)‖ ^ 2 ∂μ +
          2 * ∫ g in Q, ‖H₂ (a t * g)‖ ^ 2 ∂μ) := mul_le_mul_of_nonneg_left hle he
      _ = _ := by ring

theorem dec_smul (c : ℂ) {H : G → ℂ} (h : Dec μ ρ a H) : Dec μ ρ a (c • H) := by
  refine ⟨h.1.const_smul c, fun Q hQ => ?_⟩
  have e : ∀ t, Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖(c • H) (a t * g)‖ ^ 2 ∂μ =
      ‖c‖ ^ 2 * (Real.exp (-(2 * ρ * t)) * ∫ g in Q, ‖H (a t * g)‖ ^ 2 ∂μ) := by
    intro t
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    rw [integral_const_mul]; ring
  refine (tendsto_congr e).2 ?_
  simpa using (h.2 Q hQ).const_mul (‖c‖ ^ 2)

theorem dec_translate (hcomm : ∀ s t, a s * a t = a t * a s) (s : ℝ) {H : G → ℂ} (h : Dec μ ρ a H) :
    Dec μ ρ a (fun g => H (a s * g)) := by
  refine ⟨h.1.comp (continuous_const.mul continuous_id), fun Q hQ => ?_⟩
  set S : Set G := (fun x => (a s)⁻¹ * x) ⁻¹' Q with hSdef
  have hS : IsCompact S := (Homeomorph.mulLeft (a s)⁻¹).isCompact_preimage.2 hQ
  have hpre : (fun x => a s * x) ⁻¹' S = Q := by ext x; simp [hSdef]
  have e : ∀ t, ∫ g in Q, ‖H (a s * (a t * g))‖ ^ 2 ∂μ = ∫ g in S, ‖H (a t * g)‖ ^ 2 ∂μ := by
    intro t
    have := (measurePreserving_mul_left μ (a s)).setIntegral_preimage_emb (measurableEmbedding_mulLeft (a s))
      (fun g => ‖H (a t * g)‖ ^ 2) S
    rw [hpre] at this
    rw [← this]
    congr 1; funext x
    rw [← mul_assoc, hcomm, mul_assoc]
  refine (tendsto_congr fun t => ?_).2 (h.2 S hS)
  simp only [e t]

end General

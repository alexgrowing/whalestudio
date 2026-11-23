import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundFiniteFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaRealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerThetaGlobalStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.XTermBound

theorem bound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ ∈ PolData B G.M, ∀ h, ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧ ∀ N : ℕ, ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ k ∈ K, ∀ l : (AE F E)ˣ,
        ∫⁻ g₀ in G₁.M.dom, ‖thetaSum F (om₁ (g₀, 1) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ))))‖ₑ ∂G₁.M.μ ≤
          C * GlobalTheory.XTermMaj.maj F E N U (l : AE F E) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K hK e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  obtain ⟨U, hU, hU0⟩ := GlobalTheory.T.config_a_stabilizer_theta_real hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ h
  obtain ⟨m, c, φ, hφ, hint⟩ := GlobalTheory.T.config_a_stabilizer_theta_finite hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ h
  obtain ⟨s, C₁, hC₁t, hC₁⟩ := GlobalTheory.T.sobolev_bound_finite_family hKP F E σ B b a' G₁ X om₁ om₁' hT₁ m φ hφ
  refine ⟨U, hU, fun N => ?_⟩
  choose Cj hCj using fun j : Fin m => GlobalTheory.T.config_a_stabilizer_theta_global hKP F E σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ h U hU (c j) N s
  refine ⟨C₁ * ENNReal.ofReal (∑ j, |Cj j|), ENNReal.mul_ne_top hC₁t ENNReal.ofReal_ne_top, ?_⟩
  intro k hk l
  set r : ℝ := (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) with hr
  by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U
  · choose f hf hfb using fun j => hCj j k hk l hl
    have hD : e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ)) = ∑ j, pureA F (f j) (φ j) := by
      funext x
      rw [hint k hk l x, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [pureA, hf j, RingEquiv.symm_apply_apply]
    have hmaj : GlobalTheory.XTermMaj.maj F E N U (l : AE F E) = ENNReal.ofReal r := by
      simp only [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hl, hr]
    have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
    rw [hD, hmaj]
    refine (hC₁ f).trans ?_
    rw [mul_assoc]
    gcongr
    rw [← ENNReal.ofReal_mul (Finset.sum_nonneg fun j _ => abs_nonneg _), Finset.sum_mul]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (abs_nonneg _) hr0)]
    refine Finset.sum_le_sum fun j _ => ENNReal.ofReal_le_ofReal ((hfb j).trans ?_)
    gcongr
    exact le_abs_self _
  · rw [hU0 k hk l hl]
    simp only [map_zero, thetaSum, Pi.zero_apply, tsum_zero, enorm_zero, lintegral_zero]
    exact zero_le

end GlobalTheory.XTermBound

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DecayNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleDecayIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFiniteDecompositionStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigASchwartzLocalEvalStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeBound

theorem coneIntegrand_bound : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      ∃ A : (AE F E)ˣ → ℝ, Integrable A μ ∧ ∀ (k : K) (l : (AE F E)ˣ) (y : Fin b × Fin (b + a') → AF F),
        ‖e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) y * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2)‖ ≤ A l := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ
  have hs : 2 ≤ (b + 2 - a') / 2 := by have := hT.geo.eBig; omega
  obtain ⟨n, g, S, f, hg, hS, hfS, hdec⟩ := GlobalTheory.T.schwartz_finite_decomposition_stable hKP F E σ B (b + 2) a' G X om om' hT K hK Ψ hΨ
  choose m hm hC' using fun i => GlobalTheory.T.config_A_schwartz_local_eval hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ (g i) (hg i) S hS
  have hM : 0 < ∏ i, m i := Finset.prod_pos fun i _ => hm i
  obtain ⟨N, hN⟩ := GlobalTheory.T.idele_decay_integrable F E ((b + 2 - a') / 2) (∏ i, m i) hs hM
  choose C hCb using fun i => hC' i N
  refine ⟨fun l => (∑ i, |C i|) * (GlobalTheory.IdeleDecay.decay F E N (∏ i, m i) l * (absE F E l : ℝ) ^ ((b + 2 - a') / 2)),
    (hN μ hμ).const_mul _, ?_⟩
  intro k l y
  have hrho : ∀ (w : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)) (φ : Fin n → (Fin (b + 2) × Fin (b + 2 + a') → AF F) → ℂ),
      G.M.co.rho B.ψ w (∑ i, φ i) = ∑ i, G.M.co.rho B.ψ w (φ i) := by
    intro w φ
    funext x
    simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]
  rw [hdec k, hrho, map_sum, Finset.sum_apply]
  have hν : ‖((X.ν l : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
  have hr : ‖(((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2))‖ = (absE F E l : ℝ) ^ ((b + 2 - a') / 2) := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  rw [norm_mul, norm_mul, hν, mul_one, hr]
  have hsum : ‖∑ i, e (G.M.co.rho B.ψ (shiftA H H' l) (pureA F (f k i) (g i))) y‖ ≤
      (∑ i, |C i|) * GlobalTheory.IdeleDecay.decay F E N (∏ i, m i) l := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (hCb i (f k i) (hfS k i) l y).trans ?_
    have h1 := GlobalTheory.IdeleDecay.decay_mono (N := N) (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) l
    have h0 := GlobalTheory.IdeleDecay.decay_nonneg N (m i) l
    calc C i * GlobalTheory.IdeleDecay.decay F E N (m i) l ≤ |C i| * GlobalTheory.IdeleDecay.decay F E N (m i) l :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ |C i| * GlobalTheory.IdeleDecay.decay F E N (∏ i, m i) l := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  calc _ ≤ (∑ i, |C i|) * GlobalTheory.IdeleDecay.decay F E N (∏ i, m i) l * (absE F E l : ℝ) ^ ((b + 2 - a') / 2) :=
        mul_le_mul_of_nonneg_right hsum (pow_nonneg (NNReal.coe_nonneg _) _)
    _ = _ := mul_assoc _ _ _

end GlobalTheory.ConeBound

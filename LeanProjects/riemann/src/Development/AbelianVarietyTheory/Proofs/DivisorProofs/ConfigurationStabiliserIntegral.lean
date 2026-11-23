import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEvaluationStabilizerIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEvaluationStabilizerVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatIntegrableStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ConeIntegrand

theorem finK : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a')
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K), IsStab B K → μK.IsHaarMeasure → IsFiniteMeasure μK := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT K μK hK hμK
  obtain ⟨K', μK', μ', hK', hc, -, -⟩ := GlobalTheory.T.theta_stabilizer_exists hKP.base F E σ B a G.V _ _ hT.base hT.geo.hV
  have hKK : K = K' := by
    ext g; rw [hK g, hK' g]
  subst hKK
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hc
  infer_instance

theorem integrable_cone_pair : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      ∀ φ ∈ schA F (Fin b × Fin (b + a')),
      letI : MeasurableSpace (Fin b × Fin (b + a') → AF F) := borel _
      ∀ μY : Measure (Fin b × Fin (b + a') → AF F), μY.IsAddHaarMeasure →
      Integrable (fun p : K × ((AE F E)ˣ × (Fin b × Fin (b + a') → AF F)) => e (G.M.co.rho B.ψ (shiftA H H' p.2.1) (om (p.1.1, 1) Ψ)) p.2.2 * (X.ν p.2.1 : ℂ) *
          ((absE F E p.2.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) * starRingEnd ℂ (φ p.2.2)) (μK.prod (μ.prod μY)) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ φ hφ
  intro μY hμY
  letI : MeasurableSpace (Fin b × Fin (b + a') → AF F) := borel _
  obtain ⟨A, hA, hAb⟩ := GlobalTheory.T.config_a_evaluation_stabilizer_integral hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ
  have hM := GlobalTheory.T.config_a_evaluation_stabilizer_vanishing hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ μY hμY
  have hφi : Integrable φ μY := GlobalTheory.T.schwartz_bruhat_integrable F _ μY hμY φ hφ
  haveI := finK hKP F E σ B (b + 2) a' G X om om' hT K μK hK hμK
  have h1 : Integrable (fun q : (AE F E)ˣ × (Fin b × Fin (b + a') → AF F) => A q.1 * ‖φ q.2‖) (μ.prod μY) :=
    hA.mul_prod hφi.norm
  have h2 : Integrable (fun p : K × ((AE F E)ˣ × (Fin b × Fin (b + a') → AF F)) => (1 : ℝ) * (A p.2.1 * ‖φ p.2.2‖)) (μK.prod (μ.prod μY)) :=
    (integrable_const (1 : ℝ)).mul_prod h1
  haveI : BorelSpace (Fin b × Fin (b + a') → AF F) := ⟨rfl⟩
  have hφc : Continuous φ := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hφ
  have hφm : AEStronglyMeasurable (fun p : K × ((AE F E)ˣ × (Fin b × Fin (b + a') → AF F)) => starRingEnd ℂ (φ p.2.2)) (μK.prod (μ.prod μY)) :=
    ((continuous_star.comp hφc).measurable.comp (measurable_snd.comp measurable_snd)).aestronglyMeasurable
  refine h2.mono' (hM.mul hφm) (Filter.Eventually.of_forall fun p => ?_)
  rw [norm_mul, RCLike.norm_conj, one_mul]
  exact mul_le_mul_of_nonneg_right (hAb p.1 p.2.1 p.2.2) (norm_nonneg _)

end GlobalTheory.ConeIntegrand

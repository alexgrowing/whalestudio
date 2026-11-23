import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationStabiliserIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.configuration_stabiliser_integral : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      ∀ φ ∈ schA F (Fin b × Fin (b + a')),
      letI : MeasurableSpace (Fin b × Fin (b + a') → AF F) := borel _
      ∀ μY : Measure (Fin b × Fin (b + a') → AF F), μY.IsAddHaarMeasure →
      Integrable (fun p : K × ((AE F E)ˣ × (Fin b × Fin (b + a') → AF F)) => e (G.M.co.rho B.ψ (shiftA H H' p.2.1) (om (p.1.1, 1) Ψ)) p.2.2 * (X.ν p.2.1 : ℂ) *
          ((absE F E p.2.1 : ℝ) : ℂ) ^ ((b + 2 - a') / 2) * starRingEnd ℂ (φ p.2.2)) (μK.prod (μ.prod μY)) := by
  first | exact @GlobalTheory.ConeIntegrand.integrable_cone_pair | exact GlobalTheory.ConeIntegrand.integrable_cone_pair | (intros; apply GlobalTheory.ConeIntegrand.integrable_cone_pair <;> assumption)

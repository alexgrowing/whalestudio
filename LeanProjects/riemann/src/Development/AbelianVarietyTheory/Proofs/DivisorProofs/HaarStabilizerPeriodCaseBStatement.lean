import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerPeriodCaseB
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_stabilizer_period_case_b : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h h₁,
        AEStronglyMeasurable (fun p : UA σ G₁.V'.J × K × (AE F E)ˣ => theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.2) (om' (p.2.1.1, h) Φ'))) p.1 h₁ * (X.ν p.2.2 : ℂ) * ((absE F E p.2.2 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) ((G₁.M'.μ.restrict G₁.M'.dom).prod (μK.prod μ)) := by
  first | exact @GlobalTheory.OuterMeas.integrand_aestronglyMeasurable | exact GlobalTheory.OuterMeas.integrand_aestronglyMeasurable | (intros; apply GlobalTheory.OuterMeas.integrand_aestronglyMeasurable <;> assumption)

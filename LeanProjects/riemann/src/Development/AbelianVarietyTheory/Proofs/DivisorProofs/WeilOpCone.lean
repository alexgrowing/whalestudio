import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerIntegralUnfoldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerIntegralFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAStabilizerIntegralConvergesStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKOp

theorem weilOp_cone : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ x : UA σ G₁.V.J × UA σ G₁.W.J,
      om₁ x (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ) =
        fun y => ∫ k, ∫ l, om₁ x (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))) y * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  have hA := GlobalTheory.T.config_a_stabilizer_integral_unfold hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ
  have hpres := (IsUWeilPair.isUSplitting hT₁.weil).pres x _ hA
  have hL : Continuous (om₁ x (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ)) :=
    continuous_of_mem_schA hpres
  have hR := GlobalTheory.T.config_a_stabilizer_integral_finite hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x
  letI : MeasurableSpace (Fin b × Fin (b + a') → AF F) := borel _
  haveI : BorelSpace (Fin b × Fin (b + a') → AF F) := ⟨rfl⟩
  have hE := GlobalTheory.T.config_a_stabilizer_integral_converges hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ x
    Measure.addHaar inferInstance
  exact (Continuous.ae_eq_iff_eq Measure.addHaar hL hR).1 hE

end GlobalTheory.ThKOp

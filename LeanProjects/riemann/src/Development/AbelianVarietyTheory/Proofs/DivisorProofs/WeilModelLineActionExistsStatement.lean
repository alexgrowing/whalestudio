import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilModelLineActionExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_model_line_action_exists : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ γ ∈ Lines σ X, ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ : SInf F (Fin n × Fin d),
      GlobalTheory.RealLift.SD (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ := by
  first | exact @GlobalTheory.RealLift.FirstLine.sd_exists | exact GlobalTheory.RealLift.FirstLine.sd_exists | (intros; apply GlobalTheory.RealLift.FirstLine.sd_exists <;> assumption)

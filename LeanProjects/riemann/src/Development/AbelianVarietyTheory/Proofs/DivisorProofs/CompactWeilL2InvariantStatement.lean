import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactWeilL2Invariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationL2Isometry
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_weil_l2_invariant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χ₁ χ₂ : Chr F E),
    B.IsGood σ → M.IsGood B.ψ → M.IsWeil B.ψ χ₁ χ₂ om → ∀ k ∈ KInf σ W B.emb, ∀ f f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) (⇑f) (⇑f₁) → ∫⁻ x, ‖f₁ x‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  first | exact @GlobalTheory.ArchimedeanCompactL2.kInf_lintegral_eq | exact GlobalTheory.ArchimedeanCompactL2.kInf_lintegral_eq | (intros; apply GlobalTheory.ArchimedeanCompactL2.kInf_lintegral_eq <;> assumption)

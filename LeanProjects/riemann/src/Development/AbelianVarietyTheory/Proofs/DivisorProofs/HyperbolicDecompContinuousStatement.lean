import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicDecompContinuous
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_decomp_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (x y : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E),
    (∀ z : Fin n → AE F E, ∃ (a b : AE F E) (w : Fin n₁ → AE F E), z = a • incV F x + incM F ι *ᵥ w + b • incV F y) →
    ∀ f : (AE F E)ˣ × UA σ J₁ → Matrix (Fin n) (Fin n) (AE F E),
      (∀ p, f p *ᵥ incV F x = (p.1 : AE F E) • incV F x ∧ f p *ᵥ incV F y = cA σ ((p.1⁻¹ : (AE F E)ˣ) : AE F E) • incV F y ∧
        f p * incM F ι = incM F ι * mat p.2) → Continuous f := by
  first | exact @GlobalTheory.LeviCont.levi_continuous | exact GlobalTheory.LeviCont.levi_continuous | (intros; apply GlobalTheory.LeviCont.levi_continuous <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement

noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def coneLin {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (v : Pl F)
    (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) (μ : Measure (idelesAt E (evFin F v)))
    (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)
    (l : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (φ : (Fin n × Fin d → Fv F v) → ℂ) (g : UA σ X.J) : ℂ :=
  ∫ t, l (ev (locOp v (M.co.rho B.ψ (partFin v (u t.1))) (locOp v (om (g, 1)) φ))) * (ν t.1 : ℂ) *
    ((absE F E t.1 : ℝ) : ℂ) ^ z ∂μ

end GlobalTheory.ThK.LemF

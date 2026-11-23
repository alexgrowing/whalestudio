import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

noncomputable section

namespace GlobalTheory.ThK.FiniteLevelDerivatives

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def derR (om : Rep σ X W) (γ : ℝ → UA σ W.J) (Φ : (Fin n × Fin d → AF F) → ℂ) : (Fin n × Fin d → AF F) → ℂ :=
  fun y => deriv (fun t => om (1, γ t) Φ y) 0

def derL (om : Rep σ X W) (γ : ℝ → UA σ X.J) (Φ : (Fin n × Fin d → AF F) → ℂ) : (Fin n × Fin d → AF F) → ℂ :=
  fun y => deriv (fun t => om (γ t, 1) Φ y) 0

def combR (om : Rep σ X W) (z : List (ℝ → UA σ W.J) →₀ ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    (Fin n × Fin d → AF F) → ℂ :=
  z.sum fun l c => c • l.foldr (derR om) Φ

def combL (om : Rep σ X W) (z : List (ℝ → UA σ X.J) →₀ ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    (Fin n × Fin d → AF F) → ℂ :=
  z.sum fun l c => c • l.foldr (derL om) Φ

def back (hσ : ∀ x, σ (σ x) = x) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) {c : E} (hc : c ≠ 0)
    (γ : ℝ → GAd σ (c • J.map σ)) : ℝ → UA σ J :=
  fun t => (toGAd hσ J hc).symm (γ t)

end GlobalTheory.ThK.FiniteLevelDerivatives

end

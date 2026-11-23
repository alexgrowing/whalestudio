import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxDoublingSchrodingerFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_doubling_schrodinger_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
      (ψ : AddChar (AF F) ℂ) (y : Fin n ⊕ Fin n → AE F E) (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E))
      (φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ),
      dd.rho ψ (Matrix.vecMulVec (incV F H'.x) y) (dd.rho ψ (incM F H'.ι * z) φ) =
        dd.rho ψ (Matrix.vecMulVec (incV F H'.x) y + incM F H'.ι * z) φ := by
  first | exact @GlobalTheory.OrthHeisPhase.rho_vecMulVec_add_orth | exact GlobalTheory.OrthHeisPhase.rho_vecMulVec_add_orth | (intros; apply GlobalTheory.OrthHeisPhase.rho_vecMulVec_add_orth <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSchwartzSetIntegralShift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_schwartz_set_integral_shift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (y : Fin d → E),
    B.IsGood σ → M.IsGood B.ψ → ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, 1 ≤ N →
    ∃ S : Set (Fn F n d), S.Finite ∧ S ⊆ schA F (Fin n × Fin d) ∧ ∀ ξ : Fin n → E, (∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o) →
      ∃ Φ ∈ S, M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F y)) Ψ =
        M.co.rho B.ψ (realAd F 1 • Matrix.vecMulVec (incV F ξ) (incV F y)) Φ := by
  first | exact @GlobalTheory.FinPartHeis.finPart | exact GlobalTheory.FinPartHeis.finPart | (intros; apply GlobalTheory.FinPartHeis.finPart <;> assumption)

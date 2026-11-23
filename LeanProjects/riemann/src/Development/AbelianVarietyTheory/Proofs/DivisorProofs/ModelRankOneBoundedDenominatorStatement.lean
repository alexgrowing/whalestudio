import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelRankOneBoundedDenominator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_rank_one_bounded_denominator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (hM : M.IsGood ψ) (x : Fin d → E), ∃ D : ℕ, 1 ≤ D ∧ ∀ β : Fin n → 𝓞 E, ∃ y z : Fin n × Fin d → 𝓞 F,
      M.co.e (incM F (Matrix.vecMulVec (fun i => (β i : E)) x)) =
        (fun k => algebraMap F (AF F) ((y k : F) / D), fun k => algebraMap F (AF F) ((z k : F) / D)) := by
  first | exact @GlobalTheory.DarbouxDenom.exists_uniform_denom | exact GlobalTheory.DarbouxDenom.exists_uniform_denom | (intros; apply GlobalTheory.DarbouxDenom.exists_uniform_denom <;> assumption)

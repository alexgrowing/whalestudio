import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLagrangianSubspaceExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_lagrangian_subspace_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), Module.finrank F E = 2 →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
      ∃ K : Submodule F (Matrix (Fin n) (Fin d) E), Module.finrank F K = n * d ∧ ∀ z ∈ K, (M.co.e (incM F z)).1 = 0 := by
  first | exact @GlobalTheory.MixedLagr.rat_first_zero_dim | exact GlobalTheory.MixedLagr.rat_first_zero_dim | (intros; apply GlobalTheory.MixedLagr.rat_first_zero_dim <;> assumption)

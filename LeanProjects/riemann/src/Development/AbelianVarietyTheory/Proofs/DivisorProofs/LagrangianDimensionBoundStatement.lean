import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDimensionBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_dimension_bound : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (L : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L ≤ Fintype.card κ := by
  first | exact @GlobalTheory.finrank_le_card_of_isotropic_prod_pi | exact GlobalTheory.finrank_le_card_of_isotropic_prod_pi | (intros; apply GlobalTheory.finrank_le_card_of_isotropic_prod_pi <;> assumption)

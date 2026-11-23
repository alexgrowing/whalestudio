import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenspaceRankOneSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_rank_one_span : ∀ {O R Λ : Type} [CommRing O] [CommRing R] [AddCommGroup Λ] [Module O Λ] [Module.Finite O Λ]
    [Module.Projective O Λ] (χ : O →+* R) (e : R ⊗[ℤ] O),
    e ∈ eigenSub (baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)) χ →
    eigenSub (baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O)) χ ≤ Submodule.span R {e} →
    eigenSub (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) χ
      = LinearMap.range (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) := by
  first | exact @GlobalTheory.EigenSplit.eigenSub_eq_range_tensorAction_of_le_span | exact GlobalTheory.EigenSplit.eigenSub_eq_range_tensorAction_of_le_span | (intros; apply GlobalTheory.EigenSplit.eigenSub_eq_range_tensorAction_of_le_span <;> assumption)

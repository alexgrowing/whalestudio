import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankEigenspaceEmbeddingOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
open scoped TensorProduct NumberField
open GlobalTheory.EigenSplit

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_eigenspace_embedding_one : ∀ {E V : Type} [Field E] [NumberField E] [CommRing V] [IsDomain V] [ValuationRing V] [CharZero V]
    {ι : Type} [Fintype ι] (σ : ι → 𝓞 E →+* V), Function.Injective σ →
    Fintype.card ι = Module.finrank ℚ E → ∀ i₀ : ι,
    Module.finrank V (eigenSub (baseChangeAction V (Module.toModuleEnd ℤ (𝓞 E) : 𝓞 E →+* Module.End ℤ (𝓞 E))) (σ i₀)) = 1 := by
  first | exact @GlobalTheory.EigenSplit.finrank_eigenSub_toModuleEnd_eq_one | exact GlobalTheory.EigenSplit.finrank_eigenSub_toModuleEnd_eq_one | (intros; apply GlobalTheory.EigenSplit.finrank_eigenSub_toModuleEnd_eq_one <;> assumption)

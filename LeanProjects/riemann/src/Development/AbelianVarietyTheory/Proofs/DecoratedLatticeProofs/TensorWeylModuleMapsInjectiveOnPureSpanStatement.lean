import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorWeylModuleMapsInjectiveOnPureSpan
import Mathlib
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedFockFormPureTensorProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModules
open Formalism.BasicNotions Formalism.L2.Forms
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_weyl_module_maps_injective_on_pure_span : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (V : ι → Type) [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)] (j : ∀ τ, V τ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ) (d : ι → ℕ) (b : ∀ τ, Module.Basis (Fin (d τ)) ℂ (V τ)), (∀ τ ξ, j τ ξ ∈ delSq ℂ n (lam τ)) → (∀ τ, ∀ p ∈ delSq ℂ n (lam τ), ∃ ξ, j τ ξ = p) → (∀ τ a a', normFock (lam τ) (j τ (b τ a)) (j τ (b τ a')) = if a = a' then 1 else 0) → ∃ Jt : (⨂[ℂ] τ, V τ) →ₗ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, Function.Injective Jt ∧ LinearMap.range Jt = CSpan lam ∧ ∀ x : (∀ τ, V τ), Jt (PiTensorProduct.tprod ℂ x) = ten (fun τ => j τ (x τ)) := by
  first | exact @GlobalTheory.TenInj.main | exact GlobalTheory.TenInj.main | (intros; apply GlobalTheory.TenInj.main <;> assumption)

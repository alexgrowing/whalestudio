import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearQuotientFactorization
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multilinear_quotient_factorization : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A P₀ Q : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup P₀] [Module ℂ P₀] [AddCommGroup Q] [Module ℂ Q] (S P : ι → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] (A₀ : Submodule ℂ A) (S₀ : ∀ i, Submodule ℂ (S i)) (NQ : Submodule ℂ Q) (p₀ : A →ₗ[ℂ] P₀) (p : ∀ i, S i →ₗ[ℂ] P i) (Ψ : A →ₗ[ℂ] MultilinearMap ℂ S Q), A₀.map p₀ = ⊤ → (∀ i, (S₀ i).map (p i) = ⊤) → (∀ a ∈ A₀, ∀ s : ∀ i, S i, (∀ i, s i ∈ S₀ i) → p₀ a = 0 → Ψ a s ∈ NQ) → (∀ a ∈ A₀, ∀ s : ∀ i, S i, (∀ i, s i ∈ S₀ i) → ∀ i, p i (s i) = 0 → Ψ a s ∈ NQ) → ∀ (m : ℕ) (a : Fin m → A) (s : Fin m → ∀ i, S i), (∀ k, a k ∈ A₀ ∧ ∀ i, s k i ∈ S₀ i) → ∑ k, p₀ (a k) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun i => p i (s k i)) = 0 → ∑ k, Ψ (a k) (s k) ∈ NQ := by
  first | exact @GlobalTheory.descend_multilinear_mod | exact GlobalTheory.descend_multilinear_mod | (intros; apply GlobalTheory.descend_multilinear_mod <;> assumption)

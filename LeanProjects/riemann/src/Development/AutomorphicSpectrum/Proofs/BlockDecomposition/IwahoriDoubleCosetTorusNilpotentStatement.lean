import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetTorusNilpotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_double_coset_torus_nilpotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → ∀ a ∈ iwahori k (Fin n), ∀ b ∈ iwahori k (Fin n), ∃ m ∈ nO k n, ∃ c ∈ iwahori k (Fin n), a * tor ϖ x * b = m * tor ϖ x * c := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.iwahori_mul_tor_mul_iwahori | exact GlobalTheory.CompanionTheory.IwJac.iwahori_mul_tor_mul_iwahori | (intros; apply GlobalTheory.CompanionTheory.IwJac.iwahori_mul_tor_mul_iwahori <;> assumption)

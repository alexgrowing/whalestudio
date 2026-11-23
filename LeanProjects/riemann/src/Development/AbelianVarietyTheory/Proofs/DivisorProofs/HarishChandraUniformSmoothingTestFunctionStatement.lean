import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraUniformSmoothingTestFunction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory
theorem _root_.GlobalTheory.T.harishChandra_uniform_smoothing_test_function : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧ ∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1 := by
  first | exact @GlobalTheory.HCAlphaEll.exists_alpha_smoothing | exact GlobalTheory.HCAlphaEll.exists_alpha_smoothing | (intros; apply GlobalTheory.HCAlphaEll.exists_alpha_smoothing <;> assumption) | exact @GlobalTheory.HCAlphaEll.foldr_replicate | exact GlobalTheory.HCAlphaEll.foldr_replicate | (intros; apply GlobalTheory.HCAlphaEll.foldr_replicate <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCuspFormsFixedLevelKtypes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_cuspForms_fixedLevel_Ktypes : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∀ (χ : Module.End ℂ (Sm E a) → ℂ) (N : ℕ) (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ α : Lie E a → ℂ, IsTest (invSet E a) α → (∀ φ ∈ formsGL E a L W {χ} N, smoothing ν α φ.1 = φ.1) → FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ formsGL E a L W {χ} N ∧ IsCuspidal φ.1}) := by
  first | exact @GlobalTheory.HCFCusp.finiteDimensional_cuspSpan | exact GlobalTheory.HCFCusp.finiteDimensional_cuspSpan | (intros; apply GlobalTheory.HCFCusp.finiteDimensional_cuspSpan <;> assumption)

import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparatelyFiniteDimFunctionsFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separately_finite_dim_functions_finite : ∀ (X Y : Type) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ → ∃ 𝓥 : Submodule ℂ (X × Y → ℂ), FiniteDimensional ℂ 𝓥 ∧ ∀ f : X × Y → ℂ, (∀ y, (fun x => f (x, y)) ∈ V₁) → (∀ x, (fun y => f (x, y)) ∈ V₂) → f ∈ 𝓥 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.ProdTrick.exists_finiteDimensional_of_slices | exact GlobalTheory.CompanionTheory.CTFin.ProdTrick.exists_finiteDimensional_of_slices | (intros; apply GlobalTheory.CompanionTheory.CTFin.ProdTrick.exists_finiteDimensional_of_slices <;> assumption)

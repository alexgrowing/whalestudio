import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDilationStableRadialElement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translation_dilation_stable_radial_element : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (W : Submodule ℂ (k → ℂ)), (∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W) → (∀ Φ ∈ W, ∀ a : kˣ, (fun x => Φ (a * x)) ∈ W) → ∀ Φ ∈ W, Φ ≠ 0 → GlobalTheory.PrinTwo.IsLC Φ → GlobalTheory.PrinTwo.IsCS Φ → ∃ R ∈ W, GlobalTheory.PrinTwo.IsLC R ∧ GlobalTheory.PrinTwo.IsCS R ∧ R 0 ≠ 0 ∧ ∀ (u : kˣ) (x : k), ValuativeRel.valuation k (u : k) = 1 → R (u * x) = R x := by
  first | exact @GlobalTheory.PrinTwo.exists_radial_mem_of_stable | exact GlobalTheory.PrinTwo.exists_radial_mem_of_stable | (intros; apply GlobalTheory.PrinTwo.exists_radial_mem_of_stable <;> assumption)

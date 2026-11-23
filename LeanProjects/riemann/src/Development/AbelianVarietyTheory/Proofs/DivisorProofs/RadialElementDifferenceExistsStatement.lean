import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RadialElementDifferenceExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WEMulNUMulTD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radial_element_difference_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (W : Submodule ℂ (k → ℂ)), (∀ Φ ∈ W, ∀ y : k, (fun x => Φ (x + y)) ∈ W) → ∀ R ∈ W, GlobalTheory.PrinTwo.IsLC R → GlobalTheory.PrinTwo.IsCS R → R 0 ≠ 0 → (∀ (u : kˣ) (x : k), ValuativeRel.valuation k (u : k) = 1 → R (u * x) = R x) → ∃ (y : k) (r : kˣ) (c : ℂ), c ≠ 0 ∧ ValuativeRel.valuation k (r : k) < ValuativeRel.valuation k y ∧ c • GlobalTheory.PrinTwo.elemDiff 0 y r ∈ W := by
  first | exact @GlobalTheory.PrinTwo.exists_smul_elemDiff_mem_of_radial | exact GlobalTheory.PrinTwo.exists_smul_elemDiff_mem_of_radial | (intros; apply GlobalTheory.PrinTwo.exists_smul_elemDiff_mem_of_radial <;> assumption)

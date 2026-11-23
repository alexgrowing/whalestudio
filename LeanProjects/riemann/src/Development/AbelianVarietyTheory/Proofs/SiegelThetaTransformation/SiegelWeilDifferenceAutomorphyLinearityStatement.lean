import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilDifferenceAutomorphyLinearity
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilDifference_automorphy_linearity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (M : ℕ) (φ : Fam E n N), 0 < M → (∀ Λ ∈ Vset E n M, IsSB (φ Λ)) → ∀ Z ∈ Hn Ψ N, (∀ γ ∈ UU E N, swd Ψ M (fun Λ => weil Ψ γ (φ Λ)) (hAct Ψ γ Z) 0 0 = hFac Ψ γ Z (0 : CM Ψ n N) 0 * swd Ψ M φ Z 0 0) ∧ (∀ β : Matrix (Fin N) (Fin N) E, ccT β = β → swd Ψ M (fun Λ x => chiH Ψ β x * φ Λ x) Z 0 0 = swd Ψ M φ (fun τ => Z τ + β.map τ.1) 0 0) ∧ (∀ ψ : Fam E n N, (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) → swd Ψ M (φ + ψ) Z 0 0 = swd Ψ M φ Z 0 0 + swd Ψ M ψ Z 0 0) ∧ (∀ c : ℂ, swd Ψ M (c • φ) Z 0 0 = c * swd Ψ M φ Z 0 0) ∧ ∀ ψ : Fam E n N, (∀ Λ ∈ Vset E n M, ψ Λ = φ Λ) → swd Ψ M ψ Z 0 0 = swd Ψ M φ Z 0 0 := by
  first | exact @GlobalTheory.SW.swd_automorphy_linear | exact GlobalTheory.SW.swd_automorphy_linear | (intros; apply GlobalTheory.SW.swd_automorphy_linear <;> assumption)

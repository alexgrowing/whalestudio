import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomAlgebraicClosureApplyEqPow
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_algebraicClosure_apply_eq_pow' : ∀ (Ω : Type) [Field Ω] (K0 : Subfield Ω) (x : Ω), Transcendental K0 x → ∀ m : ℕ, 0 < m → ∃ τ : Ω →ₐ[K0] AlgebraicClosure Ω, τ x = algebraMap Ω (AlgebraicClosure Ω) x ^ m := by
  first | exact @GlobalTheory.exists_algHom_algebraicClosure_apply_eq_pow | exact GlobalTheory.exists_algHom_algebraicClosure_apply_eq_pow | (intros; apply GlobalTheory.exists_algHom_algebraicClosure_apply_eq_pow <;> assumption)

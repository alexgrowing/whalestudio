import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_types_idempotent_coefficients : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (χ : Chi B.toPre) (nd : NData B.R B.host W.what₂) (A : NAut nd), IsEmpty nd.Loc → HasChi nd χ → (∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p) → (∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p) → (GoodChi B.toPre χ ∨ ((∀ μ, W.eOp μ = 0) ∧ ∀ μ j, W.eMt μ j = 0)) → ∃ T : NTypes A, T.IdempotentMatchesAction ∧ ∀ x, ∃ y : ↥B.LL0, B.embLL (y : B.LL) = T.e0.coeff x := by
  first | exact @GlobalTheory.MemN.TypesInhab.exists_nTypes | exact GlobalTheory.MemN.TypesInhab.exists_nTypes | (intros; apply GlobalTheory.MemN.TypesInhab.exists_nTypes <;> assumption)

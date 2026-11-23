import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicUnipotentLabels
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_automorphic_unipotent_labels : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂), IsEmpty nd.Loc → ∃ A : NAut nd, (∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p) ∧ ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p := by
  first | exact @GlobalTheory.MemN.exists_nAut_unramified | exact GlobalTheory.MemN.exists_nAut_unramified | (intros; apply GlobalTheory.MemN.exists_nAut_unramified <;> assumption)

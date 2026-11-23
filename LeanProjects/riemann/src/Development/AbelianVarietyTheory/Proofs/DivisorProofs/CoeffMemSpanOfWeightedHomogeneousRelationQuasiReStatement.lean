import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSpanOfWeightedHomogeneousRelationQuasiRe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_span_of_weightedHomogeneous_relation_quasiRegular : ∀ {R : Type} [CommRing R] {n : ℕ} (z : Fin n → R) (w : Fin n → ℕ), (∀ i, 1 ≤ w i) →
    IsQuasiRegularSeq R z → ∀ (D : ℕ) (F : MvPolynomial (Fin n) R),
    F.IsWeightedHomogeneous w D → MvPolynomial.eval z F = 0 →
    ∀ α : Fin n →₀ ℕ, F.coeff α ∈ Ideal.span (Set.range z) := by
  first | exact @GlobalTheory.weightedRelation_coeff_mem_span | exact GlobalTheory.weightedRelation_coeff_mem_span | (intros; apply GlobalTheory.weightedRelation_coeff_mem_span <;> assumption)

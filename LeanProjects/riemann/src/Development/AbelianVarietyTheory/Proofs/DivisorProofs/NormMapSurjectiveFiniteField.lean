import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLatticePrimeScaling
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_surjective_finite_field : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), ∃ δ : GL (Fin n) F', (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧ nrm s δ = incl F F' n γ := by
  first | (exact @GlobalTheory.Shin.NormSurj.nrm_surj_adjoin) | (exact GlobalTheory.Shin.NormSurj.nrm_surj_adjoin) | (intros; apply GlobalTheory.Shin.NormSurj.nrm_surj_adjoin  <;> assumption)

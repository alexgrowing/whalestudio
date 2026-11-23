import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinConjInPar
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inPar_conj_of_mem_adjoin_incl_of_inPar_conj : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] (a n : ℕ) (γ y₀ : GL (Fin n) F) (δ : GL (Fin n) F'), (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} → InPar a (y₀⁻¹ * γ * y₀) → InPar a ((incl F F' n y₀)⁻¹ * δ * incl F F' n y₀) := by
  first | (exact @GlobalTheory.adjoin_conj_inPar) | (exact GlobalTheory.adjoin_conj_inPar) | (intros; apply GlobalTheory.adjoin_conj_inPar <;> assumption)

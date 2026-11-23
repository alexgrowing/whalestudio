import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TracePairingGeDetImPowHermitianHalfSpace
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_ge_detIm_pow_hermitianHalfSpace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ N c : ℕ, 0 < N → 0 < c → ∃ k : ℝ, 0 < k ∧ ∀ T : Matrix (Fin N) (Fin N) E, ccT T = T → Den c T → (∀ τ : Ψ, (T.map τ.1).PosDef) → ∀ Z ∈ Hn Ψ N, k * detIm Z ^ (1 / ((Ψ.card * N : ℕ) : ℝ)) ≤ ∑ τ : Ψ, (T.map τ.1 * imH (Z τ)).trace.re := by
  first | exact @GlobalTheory.SW.TracePair.trace_ge | exact GlobalTheory.SW.TracePair.trace_ge | (intros; apply GlobalTheory.SW.TracePair.trace_ge <;> assumption)

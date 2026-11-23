import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureConjugationInvariant
import Mathlib

open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_measure_conjugation_invariant : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G) [Countable Q] (m : G), IsClosed (N : Set G) → (∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) → (∀ n ∈ N, m * n * m⁻¹ ∈ N ∧ m⁻¹ * n * m ∈ N) → (∀ q ∈ Q, m⁻¹ * q * m * q⁻¹ ∈ N) → ∀ νN : Measure N, νN.IsHaarMeasure → ∀ E : Set N, IsFundamentalDomain (Q.subgroupOf N) E νN → νN E ≠ 0 → νN E ≠ ⊤ → ∀ c : ENNReal, c ≠ 0 → c ≠ ⊤ → (∀ S : Set N, c * νN (Subtype.val ⁻¹' ((fun g => m⁻¹ * g * m) '' (Subtype.val '' S))) = νN S) → Q.map (MulAut.conj m⁻¹).toMonoidHom ≤ Q ⊔ N ∧ ∃ ν : Measure ↥(Q ⊔ N), SFinite ν ∧ MeasurePreserving (fun p : ↥(Q ⊔ N) => p⁻¹) ν ν ∧ (∀ γ ∈ Q.subgroupOf (Q ⊔ N), MeasurePreserving (fun p : ↥(Q ⊔ N) => γ * p) ν ν) ∧ (∀ γ ∈ (Q.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (Q ⊔ N), MeasurePreserving (fun p : ↥(Q ⊔ N) => γ * p) ν ν) ∧ ∃ E₁ E₂ : Set ↥(Q ⊔ N), IsFundamentalDomain (Q.subgroupOf (Q ⊔ N)) E₁ ν ∧ IsFundamentalDomain ((Q.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (Q ⊔ N)) E₂ ν ∧ c * ν E₂ = ν E₁ ∧ ν E₁ ≠ 0 ∧ ν E₁ ≠ ⊤ := by
  first | exact @GlobalTheory.SupMeas.exists_supMeas | exact GlobalTheory.SupMeas.exists_supMeas | (intros; apply GlobalTheory.SupMeas.exists_supMeas <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizingElementFundamentalDomainScaling
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupMeas

open MeasureTheory Pointwise
open GlobalTheory.SupMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizing_element_fundamental_domain_scaling : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Q : Subgroup G) (m : G), IsClosed (N : Set G) → (∀ n ∈ N, m * n * m⁻¹ ∈ N ∧ m⁻¹ * n * m ∈ N) → ∀ (νN : Measure N) (E : Set N), IsFundamentalDomain (Q.subgroupOf N) E νN → ∀ c : ENNReal, c ≠ 0 → (∀ S : Set N, c * νN (Subtype.val ⁻¹' ((fun g => m⁻¹ * g * m) '' (Subtype.val '' S))) = νN S) → IsFundamentalDomain ((Q.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf N) (Subtype.val ⁻¹' ((fun g => m⁻¹ * g * m) '' (Subtype.val '' E))) νN := by
  first | exact @GlobalTheory.SupMeas.isFundamentalDomain_conj_inv | exact GlobalTheory.SupMeas.isFundamentalDomain_conj_inv | (intros; apply GlobalTheory.SupMeas.isFundamentalDomain_conj_inv <;> assumption)

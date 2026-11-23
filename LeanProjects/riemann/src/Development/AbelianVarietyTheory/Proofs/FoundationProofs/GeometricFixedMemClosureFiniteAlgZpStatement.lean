import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricFixedMemClosureFiniteAlgZp
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_fixed_mem_closure_finite_algZp : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ x : Ω, (∀ g ∈ Ggeo p Ω, g x = x) → ∃ S : Finset Ω, (∀ s ∈ S, IsAlgZp p s) ∧
    x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) := by
  first | exact @GlobalTheory.K5.GeoFix.fixed_mem_closure | exact GlobalTheory.K5.GeoFix.fixed_mem_closure | (intros; apply GlobalTheory.K5.GeoFix.fixed_mem_closure <;> assumption)

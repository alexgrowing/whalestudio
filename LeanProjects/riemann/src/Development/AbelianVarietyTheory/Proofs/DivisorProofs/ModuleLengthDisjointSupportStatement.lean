import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleLengthDisjointSupport
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_length_disjoint_support : ∀ {X : Scheme.{0}} (F : X.Modules) [IsFiniteQC F] (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] {ι : Type} [Fintype ι] (W : ι → X.Opens), support F ⊆ ⋃ i, (W i : Set X) → (∀ i j, i ≠ j → ∀ x ∈ support F, x ∈ W i → x ∉ W j) → Module.length R (sectionsOn F ⊤) = ∑ i, Module.length R (sectionsOn F (W i)) := by
  first | exact @GlobalTheory.length_sectionsOn_top_eq_sum_of_separating | exact GlobalTheory.length_sectionsOn_top_eq_sum_of_separating | (intros; apply GlobalTheory.length_sectionsOn_top_eq_sum_of_separating <;> assumption)

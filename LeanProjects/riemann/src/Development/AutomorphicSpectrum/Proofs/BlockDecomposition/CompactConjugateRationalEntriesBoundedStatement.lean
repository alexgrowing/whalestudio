import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjugateRationalEntriesBounded
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_conjugate_rational_entries_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (g₀ : GA E a)
    (Q : Set (GA E a)), IsCompact Q → ∀ n₀ : ℕ, ∃ (Qf : Set (Af E)) (C : ℝ), IsCompact Qf ∧ 0 ≤ C ∧
      ∀ (y : GL (Fin a) (Cinf E)) (γ : GL (Fin a) E) (n : ℤ), |n| ≤ n₀ →
        (g₀ * infGL E a y)⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * (g₀ * infGL E a y) ∈ Q →
        ∀ i j, algebraMap E (Af E) (γ.val i j) ∈ Qf ∧ ∀ w : InfinitePlace E, w (γ.val i j) ≤ C * height y ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GrowthEntries.entries_bound | exact GlobalTheory.CompanionTheory.GrowthEntries.entries_bound | (intros; apply GlobalTheory.CompanionTheory.GrowthEntries.entries_bound <;> assumption)

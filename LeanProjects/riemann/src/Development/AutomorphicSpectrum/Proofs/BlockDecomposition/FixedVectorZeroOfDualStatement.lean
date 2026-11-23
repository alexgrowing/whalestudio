import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedVectorZeroOfDual
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_vector_zero_of_dual : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ u ∈ fixed π J, (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l u = 0) → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed | exact GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed | (intros; apply GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed <;> assumption)

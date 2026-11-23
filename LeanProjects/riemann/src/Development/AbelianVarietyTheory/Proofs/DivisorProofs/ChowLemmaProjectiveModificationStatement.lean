import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowLemmaProjectiveModification
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chow_lemma_projective_modification : ∀ (R : Type) [CommRing R] [IsNoetherianRing R], ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Nonempty W → ∃ (W' P : Scheme.{0}) (π : W' ⟶ W) (q : W' ⟶ P) (s : P ⟶ Spec (CommRingCat.of R)) (U : W.Opens), IsProper π ∧ (U : Set W).Nonempty ∧ IsIso (π ∣_ U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver s ∧ IsImmersion q ∧ q ≫ s = π ≫ f := by
  first | exact @GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver | exact GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver | (intros; apply GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver <;> assumption)

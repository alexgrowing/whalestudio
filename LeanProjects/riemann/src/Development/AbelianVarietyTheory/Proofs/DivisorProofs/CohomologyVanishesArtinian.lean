import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionToSiegelDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishes_artinian : ∀ (q : ℕ) (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (n i : ℤ), (∀ M : MaximalSpectrum K, Subsingleton (Ht q (sp (K ⧸ M.asIdeal)) n i)) → Subsingleton (Ht q (sp K) n i) := by
  first | (exact @GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian) | (exact GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian) | (intros; apply GlobalTheory.EtC.ArtCoh.ht_subsingleton_artinian <;> assumption)

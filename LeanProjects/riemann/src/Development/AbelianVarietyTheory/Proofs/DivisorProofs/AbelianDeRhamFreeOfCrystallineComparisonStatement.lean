import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamFree := by
  first | exact @GlobalTheory.Proof.abelianDeRhamFree_of_hodge | exact GlobalTheory.Proof.abelianDeRhamFree_of_hodge | (intros; apply GlobalTheory.Proof.abelianDeRhamFree_of_hodge <;> assumption)

import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeOfCrystallineComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineEqDeRhamOfSmoothLiftComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHodgeDeRhamOfCrystallineLiftStatement

namespace GlobalTheory.Published

theorem abelianDeRhamStructure_crystallineDeRham_of_hypotheses :
    CrystallineSmoothLift → AbelianHodgeDeRham → AbelianDeRhamStructure ∧ CrystallineDeRham :=
  fun hL hH =>
    ⟨⟨GlobalTheory.Proof.abelianDeRhamFree_of_hodge hL hH, GlobalTheory.T.abelian_hodge_de_rham_of_crystalline_lift hL hH,
      GlobalTheory.AbelianBaseChange.abelianDeRham_baseChange_of_smoothLift hL hH⟩,
     GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift hL⟩

end GlobalTheory.Published

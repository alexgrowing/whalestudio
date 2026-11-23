import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineEqDeRhamOfSmoothLiftComparisonStatement

namespace GlobalTheory

theorem abelianDualCrystal_of_dual_of_smoothLift :
    GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianDualCrystal :=
  fun h₁ h₂ => ⟨h₁, GlobalTheory.T.crystalline_eq_deRham_of_smoothLift_comparison h₂⟩

end GlobalTheory

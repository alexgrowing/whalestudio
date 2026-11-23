import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.HomExtDvrSt
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian
open ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory

theorem homExtDvr_and_laws : Out.HomExtDvrSt ∧ Out.Laws7 := by
  have h : Out.HomExtDvrSt := fun T _ _ _ G G' _ _ hG hG' φ hφ =>
    GlobalTheory.existsUnique_hom_extension_semiAbelian T (FractionRing T) G G' hG hG' φ hφ
  exact ⟨h, ⟨h⟩⟩

end GlobalTheory

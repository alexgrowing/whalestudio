import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelKernelBoundedRepresentableOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelKernelBoundedRepresentable_of_coprime : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → SDRep h M d := by
  first | (exact @GlobalTheory.UPel.HT.sdRep_of_coprime) | (exact GlobalTheory.UPel.HT.sdRep_of_coprime) | (intros; apply GlobalTheory.UPel.HT.sdRep_of_coprime  <;> assumption)

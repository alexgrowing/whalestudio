import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftUnique
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_lift_unique : ∀ (ι : Type) [Fintype ι] (N : ℕ) (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ι → Vert.Flag ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))) N) (g₁ g₂ : T ⟶ Fl ι N), Lifts g fl' g₁ → Lifts g fl' g₂ → g₁ = g₂ := by
  first | exact @GlobalTheory.FlagZ.Univ.Uniq.lifts_unique | exact GlobalTheory.FlagZ.Univ.Uniq.lifts_unique | (intros; apply GlobalTheory.FlagZ.Univ.Uniq.lifts_unique <;> assumption)

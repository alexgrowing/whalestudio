import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinitePointsCarryLatticeVacuumToMovedVacuum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePoints_carry_latticeVacuum_to_moved_vacuum : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeak C.ψ S T om → ∀ w : D.host.E, IsIntegral ℤ w → w + cc w = 1 → IdemTwo w → ∀ (M : ℕ), ∀ Λ ∈ Vset D.host.E S.rank M, ∀ Λ' ∈ Vset D.host.E S.rank M, ∀ L L' : Lt D.host.E T.rank, SelfD C.X L → SelfD C.X L' → ∀ h ∈ GfC S, ∀ g ∈ GfC T, IsMov (fmtC S h) Λ Λ' → IsMov (fmt T g) L L' → ∀ v v', IsVac C.X C.bas w (tens Λ L) v → IsVac C.X C.bas w (tens Λ' L') v' → ∀ B, C.IsB B → ∃ c : ℂ, ‖c‖ = 1 ∧ om (h, g) (C.Th (C.xB B) v) = c • (C.Th (C.xB B) v') := by
  first | exact @GlobalTheory.Ker.om_Th_vac | exact GlobalTheory.Ker.om_Th_vac | (intros; apply GlobalTheory.Ker.om_Th_vac <;> assumption)

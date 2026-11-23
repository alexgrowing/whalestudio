import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFlagCellFrame
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FlagZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_flag_cell_frame : ∀ (ι : Type) [Fintype ι] (N : ℕ) (w : ι → Equiv.Perm (Fin N)) (τ : ι) (l : Fin (N + 1)), ∃ e : Fin l → Γ(GlobalTheory.FlagZ.Univ.F ι N τ l, GlobalTheory.FlagZ.TautCell.cellU w), GlobalTheory.VB.IsFrame e ∧ ∀ j, (GlobalTheory.FlagZ.Univ.sub ι N τ l).incl.app (GlobalTheory.FlagZ.TautCell.cellU w) (e j) = GlobalTheory.FlagZ.TautCell.colU w τ (Fin.castLE l.is_le j) := by
  first | exact @GlobalTheory.FlagZ.TautCell.exists_isFrame_step_cell | exact GlobalTheory.FlagZ.TautCell.exists_isFrame_step_cell | (intros; apply GlobalTheory.FlagZ.TautCell.exists_isFrame_step_cell <;> assumption)

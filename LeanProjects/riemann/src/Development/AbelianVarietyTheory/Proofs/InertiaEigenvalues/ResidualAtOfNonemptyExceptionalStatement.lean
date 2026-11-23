import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAtOfNonemptyExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_at_of_nonempty_exceptional : GlobalTheory.NLink.Hypotheses₂ → GlobalTheory.HeightCounting.HtCard → PrN → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), WitMv (prmR N S Γ).s → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → (AtMem hL fun _ _ _ _ w Z _ _ _ nch _ _ => GlobalTheory.NFacts.Facts (w.D Z) nch) → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => GlobalTheory.NLink.BoundAtTwoAndThreeForFamily Fm) → RL.At (prmR N S Γ) (fun Q L => R1.PredicateAtBundlePoints Q L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  first | exact @GlobalTheory.NLink.CloseMem.main | exact GlobalTheory.NLink.CloseMem.main | (intros; apply GlobalTheory.NLink.CloseMem.main <;> assumption)

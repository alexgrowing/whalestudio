import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalInvariantsMatchSemisimple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_invariants_match_semisimple : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ (π : D.naut.CG a) (s : ℝ), D.naut.csd (D.naut.tw π D.naut.etaT) → D.naut.ralg (D.naut.tw π D.naut.etaT) → (∃ m : ℤ, s = (m : ℝ) + 1 / 2) → ∀ ρ : G D.host.E D.nd.Om →* GL (Fin a) (D.nd.O i), GlobalTheory.LocalInv.Cont D.nd i ρ → IsSSRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) → GlobalTheory.LocalInv.Matches D.nd D.naut i ρ π (s + (1 - (a : ℝ)) / 2) → ∀ w, GlobalTheory.LocalInv.wd D.nd D.naut i ρ w = D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2) ∧ (w ∈ placesOver D.host.E (D.nd.l i) → GlobalTheory.LocalInv.DeRham D.nd D.naut i ρ w) := by
  first | exact @GlobalTheory.TwistLG.localGlobal_twist | exact GlobalTheory.TwistLG.localGlobal_twist | (intros; apply GlobalTheory.TwistLG.localGlobal_twist <;> assumption)

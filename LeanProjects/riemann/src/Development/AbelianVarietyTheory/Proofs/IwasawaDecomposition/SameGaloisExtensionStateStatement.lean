import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameGaloisExtensionState
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_galois_extension_state : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B' f' _ w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P), StrictHenselianAcyclic hL x → ∀ (P' : Pre2 K w'), Ext P.z P'.z → ∀ x' : St P', LI hL x' → SameGal (Dof x) (Dof x') → ∃ x'' : St P', Nonempty (SeriesLevel hL x'') ∧ Carried (Dof x) (Dof x'') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x'' := by
  first | exact @GlobalTheory.HeightCounting.Up.mvB_carry | exact GlobalTheory.HeightCounting.Up.mvB_carry | (intros; apply GlobalTheory.HeightCounting.Up.mvB_carry <;> assumption)

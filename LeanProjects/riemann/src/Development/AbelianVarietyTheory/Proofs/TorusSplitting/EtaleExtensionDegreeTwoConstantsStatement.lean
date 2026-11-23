import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaleExtensionDegreeTwoConstants
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleExtension_degreeTwo_constants : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D), (2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f) → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → 1 ≤ q → Real.log q ≤ 70 * large₂.sc.L → ETEx h (WeightFamilies.PPv D large₂ 200000 2) (EtArch h (I2.th (E := D.host.E) q R0) (200000 * zBase large₂ ^ 2)) := by
  first | exact @GlobalTheory.EtaAn.etEx_deg_two | exact GlobalTheory.EtaAn.etEx_deg_two | (intros; apply GlobalTheory.EtaAn.etEx_deg_two <;> assumption)

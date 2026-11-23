import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsCuspFormFourClausesExplicitConstant
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspForm_four_clauses_explicitConstant : ∀ (D : D7) (T : Top D) (h : LawsP T) (DF q : ℕ) (R0 P tableLineDegreeTwo : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → (∀ j, InR D j → p16 D.host.E D.R.r q D.R.m 5 (max 1 (Fintype.card (T.U j T.σ₀).Comp) * 5 ^ (8 * I2.PT.f D.host.E * D.R.r ^ 2)) ≤ min P tableLineDegreeTwo) → 0 ≤ P → ETEx h P (EtArch h (I2.th (E := D.host.E) q R0) tableLineDegreeTwo) := by
  first | exact @GlobalTheory.EtaAn.exists_form_four_clauses | exact GlobalTheory.EtaAn.exists_form_four_clauses | (intros; apply GlobalTheory.EtaAn.exists_form_four_clauses <;> assumption)

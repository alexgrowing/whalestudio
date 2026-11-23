import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductFormValuationBound
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaProductForm_valuation_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)) (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → LatMod (T.Q.Dw j) (5 ^ 4)), Nat.card (LevGrp (T.Q.Dw j) (5 ^ 4)) = 2 * 5 ^ 4 * i → Spans xs → IsEtaRule (T.Q.Xo j) T.Q.c 5 cf xs η.1 → EtVal h j ⟨h1, h2.le⟩ i η := by
  first | exact @GlobalTheory.EtaVal.etVal_of_isEtaRule | exact GlobalTheory.EtaVal.etVal_of_isEtaRule | (intros; apply GlobalTheory.EtaVal.etVal_of_isEtaRule <;> assumption)

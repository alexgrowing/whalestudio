import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.RegularityR1ValuedPoints
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETExSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.FormAtOfClause

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaInt

theorem etVal_integral :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)), (Formalism.MainNotions.ModuliIntegralCharts.H1.EtVal (recPJ h j hj) i η ↔ Formalism.L2.Pj.EtVal h j hj i η) ∧ (∀ la (y : (recPJ h j hj).Pt la), 0 ≤ (recPJ h j hj).phiC la y) ∧ (Formalism.L2.Pj.EtVal h j hj i η → IntAlg η.1 ∧ η ∈ (recB h.toLawsCore).Mlat j (wEt D j i)) := by
  intro D T h j hj i η
  refine ⟨Iff.rfl, GlobalTheory.EtaValuationTest.phiC_nonneg _, fun hv => ?_⟩
  have hm : η ∈ (recB h.toLawsCore).Mlat j (wEt D j i) :=
    GlobalTheory.EtaValuationTest.mem_Mlat (recPJ h j hj) i η hv
  refine ⟨?_, hm⟩
  have h0 := ((recPJ h j hj).Mlat_eq _ η).1 hm
  refine (nonneg_iff_of_liesTotal (T.G.liesTotal h.points_condition h.bc66 hj) η.1).2 fun la y => ?_
  exact le_of_le_of_eq (h0 la y) (recPJ_vAt_inc h j hj la y _ η)

end GlobalTheory.EtaInt

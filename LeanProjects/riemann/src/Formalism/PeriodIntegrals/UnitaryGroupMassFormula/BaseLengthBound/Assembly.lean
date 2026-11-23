import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.LenBaseOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseMemHK
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorRep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseSmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseVan
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.Column
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.UInjOfColumn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.HasseOpSmul

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PoleLengthBounds

theorem filtLenGr_holds : FiltLenGr := by
  intro R W _ _ _ F a hF h0 ha V _ _ φ hker M N P Q hNM hP hQ
  refine filtration_length_bound R W F a hF h0 ha V φ hker M N P Q hNM
    (fun k hk => Submodule.map_le_iff_le_comap.2 fun x hx => hP k hk x hx) (fun k hk v hv => ?_)
  obtain ⟨x, hx, rfl⟩ := hQ k hk v hv
  exact Submodule.mem_map_of_mem hx

theorem monoCount_holds : MonoCount := sum_antidiagonalTuple

theorem lenBase_of_steps (hTR : TaylorRep) (hTH : TaylorHasse) (hHS : HasseSmul) (hHV : HasseVan) (hUI : UInj)
    (hUB : UBall) (hAR : AARep) :
    ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j},
      LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  lenBase_of filtLenGr_holds monoCount_holds fkFilt_holds (grBound_of hTR hTH hHS hHV hUI hUB hAR)

theorem lenBase_of_taylorHasse (hTH : TaylorHasse) :
    ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j},
      LenBase (X := X) (ka := ka) (wL := wL) (wF := wF) :=
  lenBase_of_steps taylorRep_holds hTH hasseSmul_holds hasseVan_holds (uInj_of_column column_holds)
    (uBall_of_column column_holds) aaRep_holds

end PoleLengthBounds

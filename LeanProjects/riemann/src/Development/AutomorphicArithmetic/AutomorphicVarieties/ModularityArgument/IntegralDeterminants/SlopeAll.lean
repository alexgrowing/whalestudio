import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeCsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.SlopeAllOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IntK

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical

namespace UpperTheory.V.Z.Int

theorem slopeAll (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : SlopeAll := slopeAllOf hL (slopeGood (slopeCsd hD))

theorem intP (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : UpperTheory.V.Br.IntP :=
  fun K _ _ _ n hn m hm _ _ π hπ _ w _ _ _ _ B hB => slopeAll hL hD K n (by omega) m hm π hπ.1 hπ.2.1 w B hB

theorem intK (hL : GlobalTheory.GalCut.QuadLift) (hD : GlobalTheory.Cong.DescOffT) : IntK :=
  fun K _ _ _ n hn m hm _ _ π hπ _ w _ _ _ _ B hB => slopeAll hL hD K n (by omega) m hm π hπ.1
    ⟨quadChar K ^ n, fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]
      exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hπ.2.1⟩ w B hB

end UpperTheory.V.Z.Int

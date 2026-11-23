import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.MemOfInduces
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.ContraPair
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open private UpperTheory.Lit.Car.regAlg_of_coh UpperTheory.Lit.Car.mem_of_induces from Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.MemOfInduces

namespace UpperTheory.Lit.Car

theorem csdMonoOdd_of (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hGK : GlobalTheory.Published.GelfandKazhdanDual)
    (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hB : GlobalTheory.Published.DeRhamPotSemistable) (h1 : LocalGlobalAboveLAlt.LocalGlobalSubnormal) :
    UpperTheory.V.Lev.CsdMonoOdd := by
  intro E Ω _ _ _ _ _ _ l _ ι a ha _ π hd hcoh
  have hreg := UpperTheory.Lit.Car.regAlg_of_coh E a π hcoh
  have hc : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired hF E a π (hGK E a π) hd
  obtain ⟨r, wt, HT, hr⟩ := hG.of_isCsd Ω ι (by omega) hreg hc
  refine ⟨r, hr.cont, hr.ss, hr.away, fun P AI hT w A h O _ _ _ Bw hj =>
    ⟨hT.elim fun T => hr.isPstAt hB T h Bw hj, fun σ hσ rc hrc => ?_⟩⟩
  exact (h1 E Ω l ι a ha π hc hreg r wt HT hr P AI hT w (UpperTheory.Lit.Car.mem_of_induces h Bw hj) A h O Bw hj σ hσ rc hrc).2.1.1

end UpperTheory.Lit.Car

end

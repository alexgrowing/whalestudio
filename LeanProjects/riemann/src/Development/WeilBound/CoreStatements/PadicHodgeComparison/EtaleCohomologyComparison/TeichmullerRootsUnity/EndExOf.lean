import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.TUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfP

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace CrystallineSemistableComparison.crystallineComparison

theorem endEx_of (hP : BocksteinBaseChangeP) : EndEx := fun hI l _ K _ =>
  have hC : Chapters := chapters_of hP
  (hP l K).elim fun Amp hA => (hC.et l K).elim fun e he =>
    (glueB l K Amp (hC.main l) (hC.compat l) (hC.c1 l)).elim fun β _ =>
      ⟨Amp, e, GlueE.emap Amp e he, he, facts l K, hI l K,
        glueL l K Amp (hC.compatH l) (hC.rin l) hC.uniq hA.1 hA.2.1, ⟨β⟩, hA.2.2.1, fun _ _ _ _ _ => rfl⟩

end CrystallineSemistableComparison.crystallineComparison

end

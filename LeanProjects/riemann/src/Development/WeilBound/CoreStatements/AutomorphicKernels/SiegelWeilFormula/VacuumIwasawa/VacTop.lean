import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.CwInvIota
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.ContinuousIns

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Avac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem vacK_of (hT : TAll) (hF : FockMem) (hO : LocOpEx) (hI : LocInst) (hA : FinAct) : VacK := by
  intro F E _ _ _ _ _ σ d R
  exact ⟨vac_K' hT hF hO hI hA R, vac_le_fock R, fun L R' => vac_res' L hT hF R R'⟩

end PositivityTheory.SiegelWeilFormula.Avac

end

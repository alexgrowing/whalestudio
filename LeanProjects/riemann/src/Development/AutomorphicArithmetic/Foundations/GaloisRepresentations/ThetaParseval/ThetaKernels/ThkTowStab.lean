import Development.WeilBound.ThetaLifts.TowerModels.StabEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowStabCpt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThKG.Tow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem stabEx_k : _root_.GlobalTheory.ThK.StabEx_k := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  have hc := _root_.PositivityTheory.ThKG.Tow.Stab.isCompact_stabK_k hB hX
  obtain ⟨μK, hμK⟩ := Stab.exists_haar_of_isCompact _ hc
  obtain ⟨μ, hμ⟩ := Stab.exists_haar_idele (F := F) (E := E)
  exact ⟨Stab.stabK B X, μK, μ, Stab.isStab_stabK B X, hc, hμK, hμ⟩
end PositivityTheory.ThKG.Tow
end
end

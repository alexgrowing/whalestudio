import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
import Development.WeilBound.ThetaLifts.TowerModels.StabCpt

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem stabEx : StabEx := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  obtain ⟨μK, hμK⟩ := Stab.exists_haar_of_isCompact (Stab.stabK (σ := σ) B X) (Stab.isCompact_stabK hB hX)
  obtain ⟨μ, hμ⟩ := Stab.exists_haar_idele (F := F) (E := E)
  exact ⟨_, μK, μ, Stab.isStab_stabK B X, Stab.isCompact_stabK hB hX, hμK, hμ⟩

end PositivityTheory.ThKG.Tow

end

import Development.WeilBound.ThetaLifts.TowerModels.DetHerm
import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardTraceAdelicAddCharLocalComponentNeOne
import Development.WeilBound.ThetaLifts.TowerModels.Hypotheses2

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem weilEx_of (h : WeilPairExists) : WeilEx := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW M hM χX χW hχX hχW hrX hrW
  have hdX := det_herm hX
  have hdW := det_skew hW
  obtain ⟨hherm, -, -, -, -, -⟩ := hX
  obtain ⟨hskew, -, -, -, -, -⟩ := hW
  obtain ⟨hcm, -, -, hstd, -, -⟩ := hB
  obtain ⟨hrat, -, -, -, -⟩ := hM
  have hψ : B.ψ ≠ 1 := by
    intro h1
    apply Tw.PsiNontriv.psiV_ne_one B.ψ hstd B.v₁
    rw [GlobalTheory.VacAny.psiV, h1]
    ext x
    simp
  exact h F E σ hcm B.ψ hstd.1 hstd.2.1 hψ n d X.J W.J hherm hdX hskew hdW M.co hrat χX χW hχX hχW
    hrX hrW

end PositivityTheory.ThKG.Tow

end

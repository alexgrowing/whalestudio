import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ImportsAlt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContSingle
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ParabolicUnipotents

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act

theorem secUnf_of_cLaw : AbsConv → CLawEx → SecUnf := by
  intro hA hL F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨t, ht⟩ := hA F E σ d L s₁ f hf he
  refine ⟨t, fun z hz nb lam 𝓖 hc hk uM ν 𝓤 hU hkU T T' hT nb' lam' 𝓖' hc' hk' => ?_⟩
  obtain ⟨w₁, cM, κ, hlaw, hw, hwf, hcM, hκ, δ, hδ, hcf⟩ := hL F E σ d R L
  have h : C5.Hyp L nb uM nb' w₁ cM δ :=
    { nb := hc.1, uM := hU.1, nb' := hc'.1, wr := hw, wf := hwf, cf := hcf, δ0 := hδ }
  obtain ⟨K, hK⟩ := C5.unf R hf z hc hU hT hc' (fun x => ht z hz nb lam 𝓖 hc hk uM ν 𝓤 hU hkU T x) h hcM hκ
  exact ⟨w₁, cM, κ, hlaw, K, fun x => hK x⟩

theorem secUnf_of : AbsConv → SecUnf := fun hA => secUnf_of_cLaw hA cLawEx

end PositivityTheory.SiegelWeilFormula.Act

end

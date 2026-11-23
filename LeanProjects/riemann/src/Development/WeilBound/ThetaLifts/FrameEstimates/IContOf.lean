import Development.WeilBound.ThetaLifts.FrameEstimates.DomContinuous
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem iCont_of (hB : ThetaBasic) (hT : GrpTop) (hE : EpsOf) (hW : DomWeil) (hS : DomSoU) (hF : SoFin) :
    PositivityTheory.ThKF.ICont := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  refine ⟨fun hw Φ hΦ => ?_, fun _ Φ hΦ => ?_⟩
  · obtain ⟨m, f, φ, hφ, rfl⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).2.1 Φ hΦ
    have hd := hW F E σ B n d X W M χX χW om r s r' s' hp hw
    rw [show M.I om (∑ i, pureA F (f i) (φ i)) = _ from funext (dom_sum hB hp hd f φ hφ hφ).2.2]
    exact continuous_finset_sum _ fun i _ => dom_continuous hB hT hE hp hd (hφ i) (hφ i) (f i)
  · obtain ⟨m, f, φ, hφ, rfl⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ
    have hd := dom_of_domSoU hS hp
    rw [show M.I om (∑ i, pureA F (f i) (φ i)) = _ from funext (dom_sum hB hp hd f φ hφ fun i => (hφ i).1).2.2]
    exact continuous_finset_sum _ fun i _ => dom_continuous hB hT hE hp hd (hφ i) (hφ i).1 (f i)

end PositivityTheory.ThKEst

end

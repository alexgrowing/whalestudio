import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstInv
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict

noncomputable section

namespace GlobalTheory.ThK.Dbl.TC

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem splitModel_of (h : PositivityTheory.KCo.DictX) : SplitModel := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' p v t
  obtain ⟨⟨ι, hι⟩, -, s2, k⟩ := h F E σ n d B X W M om χX χW p.base ⟨_, _, p.herm⟩ ⟨_, _, p.skew⟩ p.weil v t
  exact ⟨s2, ι, hι.bij, fun g hg => ⟨Matrix.GeneralLinearGroup.map (piW t) g.1, (k ι hι).1 g hg _ rfl⟩, (k ι hι).2⟩

theorem splitModel : SplitModel := splitModel_of PositivityTheory.KCo.dictionary_extended

end GlobalTheory.ThK.Dbl.TC

end

import Development.WeilBound.CoreStatements.AutomorphicKernels.ArchimedeanJacquetFirstTerm.ArchimedeanWhittakerTrace.LZfcCore

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kfour

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fourierZero : FourierZero := by
  intro F E _ _ _ _ _ σ d nb lam 𝓖 hc f hf hper hfc
  funext g
  exact PositivityTheory.FTA.ZFC.fc_inj_pt_per d.ok.good d.b nb lam 𝓖 d.ok.frame hc f hf hper g fun T => hfc T g

end PositivityTheory.SiegelWeilFormula.kfour

end

import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}

theorem exists_cover (B : Base F E) (hB : B.IsGood σ) (hb : IsFrame2 σ Y b) :
    ∃ C : Set (nA σ Y b), IsCompact C ∧ ∀ β : nA σ Y b, ∃ ν : nF σ Y b, β + (ν : nA σ Y b) ∈ C := by
  obtain ⟨K, hK, hKx⟩ := PositivityTheory.SiegelWeilFormula.kfour.nF_cocompact (PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good hB) hb
  refine ⟨K, hK, fun β => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hKx β
  exact ⟨⟨γ, hγ⟩, by rwa [add_comm]⟩

end PositivityTheory.SiegelWeilFormula.kunf

end

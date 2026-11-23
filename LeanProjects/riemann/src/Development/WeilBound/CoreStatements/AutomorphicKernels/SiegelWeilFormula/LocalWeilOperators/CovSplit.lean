import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ExistsInsW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.CovSplit

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SD

variable (d : SD σ)

theorem cov_split (w : InfinitePlace F) (ins : Matrix (Fin d.m) (Fin d.n) ℂ → Mx F E d.m d.n)
    (hins : ∀ M, d.cw w (ins M) = M ∧ (∀ w', w' ≠ w → d.cw w' (ins M) = 0) ∧ finOne F • ins M = 0)
    (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) :
    (∀ f ∈ d.schM, Integrable f ν) ∧ ∃ (c : ℝ) (ν₀ : Measure (d.restW w)), 0 < c ∧
      ∀ G : Mx F E d.m d.n → ℂ, Integrable G ν →
        ∫ X, G X ∂ν = c * ∫ v : Fin d.m → Fin d.n → ℂ, ∫ Z : d.restW w, G (ins (Matrix.of v) + Z.1) ∂ν₀ :=
  KFock.cov_split d w ins hins ν hν

end SD

end PositivityTheory.SiegelWeilFormula

end

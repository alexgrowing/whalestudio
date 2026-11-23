import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

noncomputable section

open MeasureTheory NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures

namespace Formalism.L2.SG.Pf.MeasCore

def StdCharExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
    ∀ x : Ainf F, psiInf F ψ x =
      Complex.exp (2 * Real.pi * Complex.I *
        ((∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))

def MWCore : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (P : Frame E n r) (T : F),
    IsCMExt F E σ → IsHermND σ J → P.IsStd σ J T →
    ∀ (μNinf : Measure (Nsub (Ainf F) σ J P)) (μHinf : Measure (Hsub (Ainf F) σ J P)),
      μNinf.IsHaarMeasure → μHinf.IsHaarMeasure →
      ∃ W : MeasW σ J P, W.IsTextNorm ∧ W.μNinf = μNinf ∧ W.μHinf = μHinf

end Formalism.L2.SG.Pf.MeasCore

import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

noncomputable section

namespace GlobalTheory.LeviNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def phase (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y u : Mx D W.rank r) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D)
    (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace))

def resNorm (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)) (f : WO V W → ℂ) (u : Mx D W.rank r) : ℂ :=
  ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x *
    starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x) ∂μ'

theorem phase_apply (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y u : Mx D W.rank r) :
    phase ψ W y u = ψ (Algebra.trace (AF D.host.F) (AE D)
      (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace)) := rfl

end GlobalTheory.LeviNorm

end

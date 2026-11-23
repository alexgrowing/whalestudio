import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe

noncomputable section
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.SplitConvTw

variable {H : Type} [Group H]

def emb (σ : H →* H) (d : H) : H →* H × H where
  toFun g := (g, (σ d)⁻¹ * σ g * σ d)
  map_one' := by simp
  map_mul' a b := by simp only [map_mul, Prod.mk_mul_mk, Prod.mk.injEq, true_and]; group

@[simp] theorem emb_fst (σ : H →* H) (d g : H) : (emb σ d g).1 = g := rfl
@[simp] theorem emb_snd (σ : H →* H) (d g : H) : (emb σ d g).2 = (σ d)⁻¹ * σ g * σ d := rfl

end GlobalTheory.CompanionTheory.SplitConvTw

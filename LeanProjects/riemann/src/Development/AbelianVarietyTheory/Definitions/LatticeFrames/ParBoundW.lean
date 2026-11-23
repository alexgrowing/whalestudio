import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParBoundW (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B s.V.rank ((s.V.rank : ℝ) / 2)

def ChainLW (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ B : GlobalTheory.LFun.Fam D.host.E,
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) →
  ∀ k < D.R.m, LNe c (c.chT (k + 1)) (chainPar c B k)

def Com.eps {D : D7} (c : Com D) (k : ℕ) : (AE D)ˣ →* Circle := if Odd k then c.η⁻¹ else 1

def ChainUp (D : D7) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → ∀ c : Com D, c.Is → ∀ s₀ : PiLocalization₂ D, s₀.Is c 0 →
    ∀ k ≤ D.R.m, ∀ (s : PiLocalization₂ D) (Θ : s.CC c →ₗ[ℂ] s₀.CC c), Reach c s₀ k s Θ → s.Is c k ∧
      ∀ ipD₀ ip₀ ipD ip, IsMet c s₀ ipD₀ ip₀ → IsMet c s ipD ip → ∀ (u : s₀.CC c) B, IsPar u B →
        ∃ x : s.CC c, (∀ y, ip y x = ip₀ (Θ y) u) ∧ IsPar x (chainPar c B k)

example {D : D7} (c : Com D) : c.eps 0 = 1 := by simp [Com.eps]

end GlobalTheory.ChainOnto

end

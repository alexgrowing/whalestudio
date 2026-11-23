import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ParBoundW
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainNS

open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def HasNS (c : Com D) (χ : (AE D)ˣ →* Circle) (B : GlobalTheory.LFun.Fam D.host.E) : Prop :=
  ∃ q ∉ c.S, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q ∧ GlobalTheory.Core.Rk.SW.NSAt B χ D.R.t q

def UpNeNS (D : D7) : Prop := ForStep D fun c k s _ p => ∀ (u : s.CC c) B, IsPar u B → LNe c (c.chT (k + 1)) B →
  HasNS c (c.chT (k + 1)) B → ∃ φ, ∃ v ∈ s.KF, p.up φ (PiLocalization₂.val u v) ≠ 0

def StepUpNS (D : D7) : Prop := ForStep D fun c k s s' p => ∀ ipD ip ipD' ip', IsMet c s ipD ip → IsMet c s' ipD' ip' →
  ∀ (u : s.CC c) B, IsPar u B → LNe c (c.chT (k + 1)) B → HasNS c (c.chT (k + 1)) B →
    ∃ x : s'.CC c, (∀ y, ip' y x = ip (p.io y) u) ∧ IsPar x (stepPar (c.chS (k + 1)) (c.chT (k + 1)) D.R.t B)

def invFam (B : GlobalTheory.LFun.Fam D.host.E) : GlobalTheory.LFun.Fam D.host.E := fun w => (B w).map (·⁻¹)

def ParBoundInv (D : D7) : Prop := ForStage D fun c _ s => ∀ (u : s.CC c) B, IsPar u B →
  GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (invFam B) s.V.rank ((s.V.rank : ℝ) / 2)

def ChainNS (D : D7) : Prop := ∀ c : Com D, c.Is → ∀ S' : Finset (HeightOneSpectrum (𝓞 D.host.F)), c.S ⊆ S' →
  ∀ B : GlobalTheory.LFun.Fam D.host.E,
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) →
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S' : Set (HeightOneSpectrum (𝓞 D.host.F)))) (invFam B) D.R.r ((D.R.r : ℝ) / 2) →
    ∀ k < D.R.m, ∃ q ∉ S', Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q ∧
      GlobalTheory.Core.Rk.SW.NSAt (chainPar c B k) (c.chT (k + 1)) D.R.t q

end GlobalTheory.ChainNS

end

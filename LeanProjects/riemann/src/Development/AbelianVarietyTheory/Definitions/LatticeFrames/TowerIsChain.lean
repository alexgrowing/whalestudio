import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepsOnto

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section OfTower

variable (W : GlobalTheory.Core.Rk.Tower D)

def comOf : Com D := ⟨W.θ, W.ψ, W.toLevCh.mu (), W.eta, W.Pg, W.triv, W.chi⟩

def stageY (j : ℕ) : PiLocalization₂ D :=
  ⟨Yc D j, parB (Ptw D) (min j D.R.m), W.MY j, W.ΛY j, W.βY j, W.datYt () j W.triv, W.νY j, W.fdY j⟩

def stageX : PiLocalization₂ D := ⟨D.sp.X', parB (Ptw D) D.R.m, W.MX, W.ΛX, W.βX, W.datXt (), W.νX, W.fdX⟩

def stepY (k : ℕ) : Step (comOf W) (stageY W k) (stageY W (k + 1)) := ⟨W.ωY k, W.vY k, W.ItY k, W.ioY k⟩

def stepX : Step (comOf W) (stageY W (D.R.m - 1)) (stageX W) := ⟨W.ωX, W.vX, W.ItX, W.ioX⟩

def TowerIsChain : Prop :=
  (comOf W).Is ∧ (∀ j < D.R.m, (stageY W j).Is (comOf W) j) ∧ (stageX W).Is (comOf W) D.R.m ∧
    (∀ k, k + 1 < D.R.m → (stepY W k).Is (k + 1)) ∧ (stepX W).Is D.R.m

end OfTower

def PiLocalization₂.InFlag (s : PiLocalization₂ D) (κ : GA D s.V) : Prop :=
  κ ∈ GfC s.V ∧ Lev.finE s.V κ ∈ Formalism.L2.DIV.parLev D.sp.cm s.V.gram s.β s.L

def PiLocalization₂.ch (s : PiLocalization₂ D) (κ : GA D s.V) : ℂ := Lev.levChi s.V s.β (Lev.flagL s.L) κ

def Moved {c : Com D} {s : PiLocalization₂ D} (κ : GA D s.V) (y y' : s.CC c) : Prop :=
  ∀ w g, PiLocalization₂.val y' w g = (s.ch κ)⁻¹ * PiLocalization₂.val y w (g * κ)

def SameBlock (s s' : PiLocalization₂ D) (κ : GA D s.V) (κ' : GA D s'.V) : Prop :=
  HEq (Formalism.L2.DIV.rTup s.β s.L (Lev.finE s.V κ)) (Formalism.L2.DIV.rTup s'.β s'.L (Lev.finE s'.V κ'))

def PairLaw (D : D7) : Prop := ForStep D fun c _ s s' p => c.P.H = ⊥ → ∀ κ κ', s.InFlag κ → s'.InFlag κ' → SameBlock s s' κ κ' →
  ∀ φ, p.ω (κ, κ') (p.pt φ) = (s.ch κ * (s'.ch κ')⁻¹) • p.pt φ

def StepEqv (D : D7) : Prop := ForStep D fun c _ s s' p => c.P.H = ⊥ → ∀ κ κ', s.InFlag κ → s'.InFlag κ' → SameBlock s s' κ κ' →
  ∀ y y' : s'.CC c, Moved κ' y y' → Moved κ (p.io y) (p.io y')

def ActCC (D : D7) : Prop := ForStage D fun c _ s => c.P.H = ⊥ →
  (∀ κ, s.InFlag κ → ∀ y : s.CC c, ∃ y', Moved κ y y') ∧ Lev.LiftsExist s.V s.β s.L

example (s : PiLocalization₂ D) (κ : GA D s.V) : SameBlock s s κ κ := HEq.rfl

end GlobalTheory.ChainOnto

end

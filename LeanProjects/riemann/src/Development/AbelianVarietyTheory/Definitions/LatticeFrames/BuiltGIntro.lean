import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SumConsecutiveRanks

noncomputable section

namespace GlobalTheory.Core.AtG

open Formalism.BasicNotions NumberField GlobalTheory.Mem GlobalTheory.Mem.Col2

def BuiltG (D : D7) (EX : ErrX D) : Prop :=
  ∃ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    I.Ok ∧ I.JetsIn ∧ I.Law0 l ∧
      (⟨D, EX.piG⟩ : Σ D' : D7, (Fin 2 → 𝓞 D'.host.E)) = ⟨I.rec7 l Z, X.piG⟩

theorem builtG_intro {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (h : I.Ok)
    (hJ : I.JetsIn) (l0 : I.Law0 l) (EX : ErrX (I.rec7 l Z)) (e : EX.piG = X.piG) : BuiltG (I.rec7 l Z) EX :=
  ⟨B, X, I, l, Z, h, hJ, l0, by rw [e]⟩

theorem builtG_ind {Q : ∀ D : D7, ErrX D → Prop}
    (H : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)), I.Ok → I.JetsIn → I.Law0 l →
      ∀ EX : ErrX (I.rec7 l Z), EX.piG = X.piG → Q (I.rec7 l Z) EX) {D : D7} {EX : ErrX D} (h : BuiltG D EX) : Q D EX := by
  obtain ⟨B, X, I, l, Z, h1, h2, h3, e⟩ := h
  have e1 : D = I.rec7 l Z := congrArg Sigma.fst e
  subst e1
  exact H B X I l Z h1 h2 h3 EX (eq_of_heq (Sigma.mk.inj_iff.1 e).2)

end GlobalTheory.Core.AtG

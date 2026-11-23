import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GlobalLocalFactorization
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharacterClosedForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined

noncomputable section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

namespace GlobalTheory.PlaceCompare

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' I : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype I] [DecidableEq I] {c : ℕ}

variable [MeasurableSpace k] [BorelSpace k]

end GlobalTheory.PlaceCompare

end

noncomputable section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

namespace GlobalTheory.PlaceCompare

def eX (κ t j : ℕ) : XI κ t j ≃ XIx (Fin κ) (Fin t) j :=
  (Equiv.sumAssoc _ _ _).symm.trans (((Equiv.refl _).sumCongr Fin.revPerm).sumCongr (Equiv.refl _))

def eY (κ t j c : ℕ) : XI κ t j ⊕ Fin c ≃ XIx (Fin κ) (Fin t) j ⊕ Fin c := (eX κ t j).sumCongr (Equiv.refl _)

def ord (κ t : ℕ) {l : ℕ} (j c : ℕ) (h : j + c = l) : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ XI κ t j ⊕ Fin c :=
  (stdOrd (Fin κ) (Fin t) j c h).trans (eY κ t j c).symm

def labIx {κ t l j : ℕ} : Ix (Fin κ ⊕ Fin l) (Fin t) j → Fin κ ⊕ ℕ ⊕ ℕ × Fin t
  | .inl (.inl a) => .inl a
  | .inl (.inr i) => .inr (.inl (i.val + 1))
  | .inr p => .inr (.inr (p.1.val, p.2))

variable {κ t l j c : ℕ}

def aOrd (h : j + c = l) : Fin κ ⊕ Fin j ⊕ Fin c → Fin κ ⊕ Fin l
  | .inl a => .inl a
  | .inr (.inl s) => .inr ⟨c + (j - 1 - s.val), by omega⟩
  | .inr (.inr i) => .inr ⟨i.val, by omega⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def diagFrame {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (b : ℕ → kˣ) (o : ι ≃ n ⊕ Fin c) : LatFrame k ι (n ⊕ Fin c) :=
  ⟨o, embA n (SplitFlip.diagGL fun i => b (i.val + 1))⟩

variable {s : ℕ} (S : SymData k s κ)

abbrev levelChain (t : ℕ) : Chain k s (XI κ t) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) (s + 2)) :=
  Chain.ofType S.P S.μ S.tame (fun j c h => typeFrame S.ϖ (ord κ t j c h)) (LatFrame.refl k _)

variable (s κ t) in

abbrev ramChain (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) :
    Chain k s (XI κ t) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin t) (s + 2)) :=
  Chain.ofTwist δ hδ η (fun j c h => plainFrame (ord κ t j c h)) (LatFrame.refl k _)

variable {δ : kˣ →* ℂˣ} (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ)

def prodShiftedUnits (b : ℕ → kˣ) (c : ℕ) : kˣ := ∏ i : Fin c, b (i.val + 1)

end GlobalTheory.PlaceCompare

end

noncomputable section

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

namespace GlobalTheory.PlaceCompare

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' m m' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype m] [DecidableEq m]
  [Fintype m'] [DecidableEq m'] {c : ℕ}

abbrev sumE (e : n ≃ m) (c : ℕ) : n ⊕ Fin c ≃ m ⊕ Fin c := e.sumCongr (Equiv.refl _)

section Frames

omit [MeasurableSpace k] [BorelSpace k]

end Frames

structure Renum {s : ℕ} {X X' : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] [∀ j, Fintype (X' j)]
    [∀ j, DecidableEq (X' j)] {Z : Type} [Fintype Z] [DecidableEq Z] (e : ∀ j, X j ≃ X' j) (T : Chain k s X Z)
    (T' : Chain k s X' Z) : Prop where
  mu : T.mu = T'.mu
  bas : ∀ j c h, reGL (sumE (e j) c) (T.bas j c h) = T'.bas j c h
  mem : ∀ j c h g, g ∈ (T.lev j c h).J ↔ reGL (sumE (e j) c) g ∈ (T'.lev j c h).J
  lam : ∀ j c h g hg hg', (T.lev j c h).lam ⟨g, hg⟩ = (T'.lev j c h).lam ⟨reGL (sumE (e j) c) g, hg'⟩
  Phi : ∀ j c h y, T.Phi j c h (y.submatrix (sumE (e (j + 1)) c) (sumE (e j) (c + 1))) = T'.Phi j c h y

end GlobalTheory.PlaceCompare

end

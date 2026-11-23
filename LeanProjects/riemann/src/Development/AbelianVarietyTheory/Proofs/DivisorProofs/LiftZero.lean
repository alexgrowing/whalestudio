import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainEmbZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainEmbSuccMulVec

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.FirstCompChain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (σ) in

structure PiLocalization₂ {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) where

  μ : Measure (unip σ Y H)

  dom : Set (unip σ Y H)

  lev : UA σ Y₁.J →* UA σ Y.J

  tor : UA σ Y.J

  w₁ : ℂ

  w₂ : ℂ

namespace PiLocalization₂

variable {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁}

def op (s : PiLocalization₂ σ Y Y₁ H) (G : UA σ Y.J → ℂ) : UA σ Y₁.J → ℂ :=
  fun h => s.w₁ * GlobalTheory.CtTyp.ctf H s.μ s.dom G (s.lev h * s.tor) + s.w₂ * GlobalTheory.CtTyp.ctf H s.μ s.dom G (s.lev h)

structure Good (s : PiLocalization₂ σ Y Y₁ H) (χa χb : Chr F E) (za zb : ℝ) : Prop where
  frame : ∃ (π : Matrix (Fin n₁) (Fin n) E) (h : GlobalTheory.ThK.FlagSemi.IsFrame σ Y.J Y₁.J H π), s.lev = h.1.levi
  haar : s.μ.IsHaarMeasure
  fund : IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unip σ Y H)) s.dom s.μ
  one : s.μ s.dom = 1
  sep : ∃ t : (AE F E)ˣ, IsLevi (W₁ := Y₁) H t 1 s.tor ∧
    ((GlobalTheory.CtTyp.twAbs χa za t : ℂˣ) : ℂ) ≠ ((GlobalTheory.CtTyp.twAbs χb zb t : ℂˣ) : ℂ) ∧
    s.w₁ = (((GlobalTheory.CtTyp.twAbs χa za t : ℂˣ) : ℂ) - ((GlobalTheory.CtTyp.twAbs χb zb t : ℂˣ) : ℂ))⁻¹ ∧
    s.w₂ = -((GlobalTheory.CtTyp.twAbs χb zb t : ℂˣ) : ℂ) *
      (((GlobalTheory.CtTyp.twAbs χa za t : ℂˣ) : ℂ) - ((GlobalTheory.CtTyp.twAbs χb zb t : ℂˣ) : ℂ))⁻¹

end PiLocalization₂

def Reg {n : ℕ} {Y : Spc F E n} (f : UA σ Y.J → ℂ) : Prop :=
  Continuous f ∧ ∀ γ ∈ ratU σ Y.J, ∀ x, f (γ * x) = f x

variable (σ) in

structure Chain {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j))
    (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))) where

  s0 : PiLocalization₂ σ W (sp 0) H'

  s : ∀ j, PiLocalization₂ σ (sp j) (sp (j + 1)) (pl j)

namespace Chain

variable {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} {sp : ∀ j : ℕ, Spc F E (d₁ - 2 * j)}
  {pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))}

def op (C : Chain σ W H' sp pl) (i : ℕ) : (UA σ W.J → ℂ) → (UA σ (sp i).J → ℂ) :=
  Nat.rec (motive := fun i => (UA σ W.J → ℂ) → (UA σ (sp i).J → ℂ)) C.s0.op (fun j T G => (C.s j).op (T G)) i

theorem op_zero (C : Chain σ W H' sp pl) (G : UA σ W.J → ℂ) : C.op 0 G = C.s0.op G := rfl

theorem op_succ (C : Chain σ W H' sp pl) (j : ℕ) (G : UA σ W.J → ℂ) : C.op (j + 1) G = (C.s j).op (C.op j G) := rfl

def lift (C : Chain σ W H' sp pl) (i : ℕ) : UA σ (sp i).J →* UA σ W.J :=
  Nat.rec (motive := fun i => UA σ (sp i).J →* UA σ W.J) C.s0.lev (fun j L => L.comp (C.s j).lev) i

theorem lift_zero (C : Chain σ W H' sp pl) : C.lift 0 = C.s0.lev := rfl

theorem lift_succ (C : Chain σ W H' sp pl) (j : ℕ) : C.lift (j + 1) = (C.lift j).comp (C.s j).lev := rfl

structure Good (C : Chain σ W H' sp pl) (X : Chars F E) (a a' p : ℕ) : Prop where
  s0 : C.s0.Good X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2)
  s : ∀ j < p, (C.s j).Good X.α X.β ((a' : ℝ) / 2) (zb a j)

def admitted (C : Chain σ W H' sp pl) (X : Chars F E) (a a' i : ℕ) (G : UA σ W.J → ℂ) : Prop :=
  Reg G ∧ (∃ fa fb, SplitZ (sp 0) H' X.α X.β ((a' : ℝ) / 2) ((a : ℝ) / 2) G fa fb) ∧
    (∀ k < i, Reg (C.op k G) ∧
      ∃ fa fb, SplitZ (sp (k + 1)) (pl k) X.α X.β ((a' : ℝ) / 2) (zb a k) (C.op k G) fa fb) ∧
    Reg (C.op i G)

end Chain

end GlobalTheory.ThK.FirstCompChain

end

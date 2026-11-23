import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.HighestDerivProd

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.RgGu.Leib

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def dpowM (n : ℕ) (s : ℝ) : Mir k n →* ℂˣ := (dpow (n + 1) s).comp (Mir k n).subtype

def mtw {n : ℕ} (τ : MRep k n) (s : ℝ) : MRep k n := ⟨τ.V, twist τ.ρ (dpowM n s)⟩

def mcast {a b : ℕ} (h : a = b) (τ : MRep k a) : MRep k b := h ▸ τ

def gres {n : ℕ} (π : GRep k (n + 1)) : MRep k n := resM k π.ρ

def phiN (ψ : AddChar k Circle) {n : ℕ} (τ : MRep k (n + 1)) : MRep k n := mtw (MRep.phiM k ψ τ) (-1 / 2)

def psiN {n : ℕ} (τ : MRep k n) : GRep k n := (⟨_, psiMinus k τ.ρ⟩ : GRep k n).tw (-1 / 2)

def prodGPn {m j : ℕ} (ρ : GRep k m) (τ : MRep k j) : MRep k (m + j) :=
  ⟨_, prodGP (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw τ (-((m : ℕ) : ℝ) / 2)).ρ⟩

def prodPGn {i t : ℕ} (τ : MRep k i) (σ : GRep k t) : MRep k (i + t) :=
  ⟨_, prodPG (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ⟩

def MIso {n : ℕ} (A B : MRep k n) : Prop := Nonempty (A.ρ.Equiv B.ρ)

def GIso {n : ℕ} (A B : GRep k n) : Prop := Nonempty (A.ρ.Equiv B.ρ)

def MExt {n : ℕ} (A B C : MRep k n) : Prop :=
  ∃ S : Subrepresentation B.ρ, Nonempty ((subQuot S ⊥).Equiv A.ρ) ∧ Nonempty ((subQuot ⊤ S).Equiv C.ρ)

end GlobalTheory.RgGu.Leib

end

import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.BZMir.Leib

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure GRep (n : ℕ) where
  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]
  ρ : Representation ℂ (GL (Fin n) k) V

attribute [instance] GRep.acg GRep.mod

variable {k}

def GRep.cast {a b : ℕ} (h : a = b) (π : GRep k a) : GRep k b := h ▸ π

def dpow (n : ℕ) (s : ℝ) : GL (Fin n) k →* ℂˣ := detChar (Fin n) (absPow k (s : ℂ))

def GRep.tw {n : ℕ} (π : GRep k n) (s : ℝ) : GRep k n := ⟨π.V, twist π.ρ (dpow n s)⟩

def GRep.prod {r t : ℕ} (π₁ : GRep k r) (π₂ : GRep k t) : GRep k (r + t) := ⟨_, prod2 rfl π₁.ρ π₂.ρ⟩

def derivB (ψ : AddChar k Circle) : (j : ℕ) → {n : ℕ} → GRep k (n + j) → GRep k n
  | 0, _, π => π
  | j + 1, _, π => ⟨_, GlobalTheory.BZMir.deriv k ψ j π.ρ⟩

variable (k)

def LeibnizRule : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (r t ℓ n : ℕ) (hn : r + t = n + ℓ) (π₁ : GRep k r) (π₂ : GRep k t), IsSmooth π₁.ρ → IsSmooth π₂.ρ →
      ∃ (F : Fin (ℓ + 2) → Subrepresentation (derivB ψ ℓ ((π₁.prod π₂).cast hn)).ρ) (e : Fin (ℓ + 1) ≃ Fin (ℓ + 1)),
        F 0 = ⊥ ∧ F (Fin.last (ℓ + 1)) = ⊤ ∧ Monotone F ∧
        ∀ a : Fin (ℓ + 1),
          if h : (e a : ℕ) ≤ r ∧ ℓ - e a ≤ t then
            ∃ (s₁ s₂ : ℝ) (hsz : (r - e a) + (t - (ℓ - e a)) = n),
              Nonempty ((subQuot (F a.succ) (F a.castSucc)).Equiv
                ((((derivB ψ (e a) (π₁.cast (Nat.sub_add_cancel h.1).symm)).tw s₁).prod
                  ((derivB ψ (ℓ - e a) (π₂.cast (Nat.sub_add_cancel h.2).symm)).tw s₂)).cast hsz).ρ)
          else F a.succ ≤ F a.castSucc

def HighestDerivProd : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (r t : ℕ) (π₁ : GRep k r) (π₂ : GRep k t), IsSmooth π₁.ρ → IsSmooth π₂.ρ →
      Nonempty ((derivB ψ (r + t) ((π₁.prod π₂).cast (zero_add (r + t)).symm)).V ≃ₗ[ℂ]
        (derivB ψ r (π₁.cast (zero_add r).symm)).V ⊗[ℂ] (derivB ψ t (π₂.cast (zero_add t).symm)).V)

end GlobalTheory.BZMir.Leib

end

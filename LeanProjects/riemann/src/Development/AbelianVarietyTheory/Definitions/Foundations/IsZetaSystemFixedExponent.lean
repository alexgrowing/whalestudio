import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def IsZetaSystemFixedExponent (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N : ℕ) [NeZero N] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ : ℕ)
    (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∀ r n : ℕ, ∃ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
    (∀ σ ∈ fixMu Ω (topMu l n r N), LiftB X l N (k - 2) n c₀ (clsBmu X l n r N x c d k g σ) (bB σ)) ∧
    ∃ b : (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
      Cv n (Y r s y) (YfB X l pr W e ψ n r N bB s y +
        (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y))

def IsZTc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N l' : ℕ) [NeZero N] [NeZero l'] (x : ZMod N) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ : ℕ)
    (YT : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∀ r n : ℕ, ∃ bB : (Ω ≃ₐ[ℚ] Ω) → X.Fn l,
    (∀ σ ∈ fixMu Ω (topMT l n r N l'), LiftB X l N (k - 2) n c₀ (clsBTmu X l n r N l' x c d k g σ) (bB σ)) ∧
    ∃ b : (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l, (∀ y i, b y i ∈ cf.O) ∧ ∀ s y,
      Cv n (YT r s y) (YfBT X l pr W e ψ n r N l' bB s (y.1 * lsqInv l l' (r + n), y.2) + (rhoK W e ψ s *ᵥ b (y * cycT l r l' s) - b y))

def IsZWc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ : ℕ)
    (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∃ Yx : ZMod N → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
    (∀ x, IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf c₀ (Yx x)) ∧ ∀ r s y, Y r s y = ∑ x, cw x • Yx x r s y

def IsZTWc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l)
    (N l' : ℕ) [NeZero N] [NeZero l'] (cw : ZMod N → Qbar l) (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ : ℕ)
    (YT : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) : Prop :=
  ∃ Yx : ZMod N → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod l')ˣ × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
    (∀ x, IsZTc X l pr W e ψ N l' x c d k g cf c₀ (Yx x)) ∧ ∀ r s y, YT r s y = ∑ x, cw x • Yx x r s y

end GlobalTheory.K4

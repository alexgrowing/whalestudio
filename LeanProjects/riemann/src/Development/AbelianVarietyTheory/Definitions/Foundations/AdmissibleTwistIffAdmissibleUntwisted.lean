import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ChiK
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr

noncomputable section

open scoped MatrixGroups Matrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def admitted {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (W : R2 Ω l) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) : Prop :=
  1 < c ∧ 1 < d ∧ Nat.Coprime c (6 * l * N) ∧ Nat.Coprime d (6 * l * N) ∧ IsUnit x ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = mat W s *ᵥ pr b) ∧
    ∃ δ : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b ∧ pr (X.diam N l q b) = δ q • pr b

def psiCyc {l : ℕ} [Fact l.Prime] (ψ : ZMod l → Qbar l) (s : Ω ≃ₐ[ℚ] Ω) : Qbar l :=
  ψ ((((cycMod (F := ℚ) (Ω := Ω) l 1 s : ZMod (l ^ 1))).val : ℕ) : ZMod l)

def AdmT {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e : ℕ) (gN : Newform (2 * e + 1)) (W : R2 Ω l) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (_gm : (ZMod l)ˣ → SL(2, ℤ))
    (ψ : ZMod l → Qbar l) : Prop :=
  1 ≤ e ∧ 1 < c ∧ 1 < d ∧ Nat.Coprime c (6 * l * N) ∧ Nat.Coprime d (6 * l * N) ∧ IsUnit x ∧
    (ψ 1 = 1 ∧ ∀ a b : (ZMod l)ˣ, ψ ((a * b : (ZMod l)ˣ) : ZMod l) = ψ a * ψ b) ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) →
      pr (X.galB l s b) = ((cycBar ℚ Ω l s : Qbar l) ^ e * (psiCyc ψ s)⁻¹) • (mat W s *ᵥ pr b)) ∧
    ∃ δ : ℕ → Qbar l, ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b ∧ pr (X.diam N l q b) = δ q • pr b

def unTw {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (e : ℕ) (χ : G ℚ Ω →* (Qbar l)ˣ) : R2 Ω l :=
  tw W (cycBar ℚ Ω l ^ e * χ⁻¹)

example {l : ℕ} [Fact l.Prime] (s : Ω ≃ₐ[ℚ] Ω) : psiCyc (fun _ : ZMod l => (1 : Qbar l)) s = 1 := rfl

example {l : ℕ} [Fact l.Prime] (e : ℕ) (ψ : ZMod l → Qbar l) (h1 : ψ 1 = 1) :
    (cycBar ℚ Ω l 1 : Qbar l) ^ e * (psiCyc (Ω := Ω) ψ 1)⁻¹ = 1 := by
  have : Fact (1 < l ^ 1) := ⟨by simpa using (Fact.out : l.Prime).one_lt⟩
  simp [psiCyc, ZMod.val_one, h1]

example {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * 0 + 1)) (W : R2 Ω l) (X : Tower Ω ε)
    (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
    (ψ : ZMod l → Qbar l) : ¬ AdmT ι 0 gN W X pr N x c d gm ψ := fun h => absurd h.1 (by omega)

end GlobalTheory.K4

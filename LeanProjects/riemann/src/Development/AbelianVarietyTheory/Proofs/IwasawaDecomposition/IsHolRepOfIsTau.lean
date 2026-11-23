import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Datum Matrix
open scoped InnerProductSpace Classical

namespace GlobalTheory.JointHarm

section Hol

variable {n : ℕ} {P : Type} [AddCommGroup P] [Module ℂ P]

def IsHolRep (ε : Fin n → Bool) (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) : Prop :=
  (∀ x, B x x = 0 → x = 0) ∧ π 1 = 1 ∧
    (∀ a ∈ GlobalTheory.Dec.KC ε, ∀ b ∈ GlobalTheory.Dec.KC ε, π (a * b) = π a * π b) ∧
    (∀ g ∈ GlobalTheory.Dec.KC ε, ∀ x y, B (π g x) y = B x (π gᴴ y)) ∧
    ∀ x y, DifferentiableOn ℂ (fun g : Fin n → Fin n → ℂ => B x (π (Matrix.of g) y))
      {g | Matrix.of g ∈ GlobalTheory.Dec.KC ε}

def IsBottom (ε : Fin n → Bool) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (μ : Fin n → ℝ) (x : P) : Prop :=
  (∀ g ∈ GlobalTheory.Dec.KC ε, IsLoUni g → π g x = x) ∧
    ∀ θ : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) x =
      Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • x

variable {ι : Type}

def IsHolFam (ε : ι → Fin n → Bool) (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
    (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) : Prop :=
  (∀ x, B x x = 0 → x = 0) ∧ ϖ 1 = 1 ∧
    (∀ a b, (∀ τ, a τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, b τ ∈ GlobalTheory.Dec.KC (ε τ)) → ϖ (a * b) = ϖ a * ϖ b) ∧
    ∀ τ, IsHolRep (ε τ) B fun g => ϖ (Pi.mulSingle τ g)

def IsBotFam (ε : ι → Fin n → Bool) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P)
    (μ : ι → Fin n → ℝ) (x : P) : Prop :=
  ∀ τ, IsBottom (ε τ) (fun g => ϖ (Pi.mulSingle τ g)) (μ τ) x

theorem isHolRep_of_isTau {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : GlobalTheory.Dec.IsTau ε abelian₂ τ w) :
    IsHolRep ε (innerₛₗ ℂ) (fun g => (τ g : W →ₗ[ℂ] W)) ∧
      IsBottom ε (fun g => (τ g : W →ₗ[ℂ] W)) (-abelian₂) w := by
  obtain ⟨-, ⟨h1, hm⟩, hd, ha, -, -, hw, hl⟩ := h
  refine ⟨⟨fun x hx => inner_self_eq_zero.1 hx, ?_, fun a ha b hb => ?_, ha, hd⟩, hl, fun θ => hw θ ⟨?_, ?_⟩⟩
  · show (τ 1 : W →ₗ[ℂ] W) = 1
    rw [h1]; rfl
  · show (τ (a * b) : W →ₗ[ℂ] W) = _
    rw [hm a ha b hb]; rfl
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [← Complex.exp_conj, ← Complex.exp_add]
  · simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

end Hol

section Fock

variable {D : D7} {m n : ℕ}

def fsub (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : PolF D m n →ₐ[ℂ] PolF D m n :=
  MvPolynomial.aeval fun v => ∑ a : Fin m, ∑ b : Fin n,
    MvPolynomial.C (if ε v.1 v.2.1 = true then k v.1 a v.2.1 * (u v.1)⁻¹ v.2.2 b
      else (k v.1)⁻¹ v.2.1 a * u v.1 b v.2.2) * MvPolynomial.X (v.1, a, b)

def detP (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) * k + (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε)).det

def detM (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) * k + (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε)).det

def fchar (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ τ, detP (ε τ) (k τ) ^ x₁ τ * detM (ε τ) (k τ) ^ x₂ τ * (u τ).det ^ x₃ τ

def fact (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (PolF D m n) :=
  fchar ε x₁ x₂ x₃ k u • (fsub ε k u).toLinearMap

def factK (n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (g : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : Module.End ℂ (PolF D m n) :=
  fact ε x₁ x₂ x₃ (fun τ => ((g τ)⁻¹)ᵀ) 1

def factU (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (PolF D m n) :=
  fact ε x₁ x₂ x₃ 1 u

def wtK (p : ℕ) (ap am : ℕ → ℕ) (x₁ x₂ : ℤ) (a : Fin m) : ℤ :=
  if (a : ℕ) < p then (ap a : ℤ) + x₁ else -(am (m - 1 - a) : ℤ) + x₂

def wtU (p q : ℕ) (ap am : ℕ → ℕ) (x₃ : ℤ) (j : Fin n) : ℤ :=
  -(if (j : ℕ) < p then (ap j : ℤ) else 0) + (if n - 1 - j < q then (am (n - 1 - j) : ℤ) else 0) + x₃

end Fock

def vact {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (u : ι → Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (Pol ℂ ι n) :=
  (∏ τ, (u τ).det ^ (-(lam τ).detShift)) • (Formalism.GradedWeylDivisibility.blockAct ℂ fun τ => (u τ)⁻¹).toLinearMap

end GlobalTheory.JointHarm

end

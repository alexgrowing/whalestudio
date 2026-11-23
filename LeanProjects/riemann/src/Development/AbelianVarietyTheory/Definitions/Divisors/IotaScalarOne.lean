import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps

noncomputable section

open WittVector Ideal Matrix GlobalTheory.Sandwich TensorProduct

namespace GlobalTheory.DetInv

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

scoped instance algA : Algebra ℤ_[p] (Ainf p O) := (ofPadic p O).toAlgebra

variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]

abbrev RL : Type := Ainf p O ⊗[ℤ_[p]] Λ

variable {p O Λ}

abbrev inA (a : Ainf p O) : RL p O Λ := algebraMap (Ainf p O) (RL p O Λ) a

def IsTheta (σ : Λ →+* O) (f : RL p O Λ →+* O) : Prop :=
  ∀ (a : Ainf p O) (l : Λ), f (a ⊗ₜ l) = fontaineTheta O p a * σ l

def IsPsi (ψ : RL p O Λ →+* RL p O Λ) : Prop :=
  ∀ (a : Ainf p O) (l : Λ), ψ (a ⊗ₜ l) = phiInv p O a ⊗ₜ l

def IsFrame {N h : ℕ} (ρ : Λ → Matrix (Fin h) (Fin h) (Ainf p O))
    (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) : Prop :=
  ∀ (l : Λ) (w : Fin N → RL p O Λ), e (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • w) = ρ l *ᵥ e w

def IsMat {N h : ℕ} (e e' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O))
    (X : Matrix (Fin h) (Fin h) (Ainf p O)) (Y : Matrix (Fin N) (Fin N) (RL p O Λ)) : Prop :=
  ∀ w, X *ᵥ e w = e' (Y *ᵥ w)

def IsProj (C : Type) [Field C] [Algebra O C] {N h : ℕ}
    (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) (f : RL p O Λ →+* O)
    (π : (Fin h → C) →ₗ[C] (Fin N → C)) : Prop :=
  ∀ w, π (fun j => algebraMap O C (fontaineTheta O p (e w j))) = fun i => algebraMap O C (f (w i))

abbrev rhoTA {ε : PreTilt O p} {h : ℕ} (D : Datum ε h Λ) (l : Λ) :
    Matrix (Fin h) (Fin h) (Ainf p O) := (D.ρT l).map (ofPadic p O)

def IotaScalar {C : Type} [Field C] {N : ℕ} (α β : Matrix (Fin N) (Fin N) C) (a : ℕ) (lam : C) :
    Prop :=
  ∀ x y : Fin N → Fin N → C, (∀ i : Fin N, (i : ℕ) < a → x i = β *ᵥ y i) →
    (∀ i : Fin N, a ≤ (i : ℕ) → y i = α *ᵥ x i) → (Matrix.of y).det = lam * (Matrix.of x).det

def Lead {R C : Type} [CommRing R] [Field C] (f : R →+* C) (ξ r : R) (n : ℕ) (c : C) : Prop :=
  ∃ s t : R, f s ≠ 0 ∧ s * r = ξ ^ n * t ∧ f t = c * f s

structure FreeForm {ε : PreTilt O p} {h : ℕ} (D : Datum ε h Λ) (N : ℕ)
    (ψ : RL p O Λ →+* RL p O Λ) where

  eT : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)

  eM : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)

  F : Matrix (Fin N) (Fin N) (RL p O Λ)

  G : Matrix (Fin N) (Fin N) (RL p O Λ)

  Ψ : Matrix (Fin N) (Fin N) (RL p O Λ)

  Ψ' : Matrix (Fin N) (Fin N) (RL p O Λ)
  frameT : IsFrame (rhoTA D) eT
  frameM : IsFrame D.ρM eM
  matF : IsMat eT eM D.F F
  matG : IsMat eM eT D.G G
  G_mul_F : G * F = (inA (mu ε) : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))
  F_mul_G : F * G = (inA (mu ε) : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))
  F_eq : F = Ψ * F.map ψ
  Ψ_mul : Ψ * Ψ' = (inA (xi ε) : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))

theorem iotaScalar_one {C : Type} [Field C] (N : ℕ) :
    IotaScalar (1 : Matrix (Fin N) (Fin N) C) 0 0 1 := by
  intro x y _ h2
  have : y = x := funext fun i => by simpa using h2 i (Nat.zero_le _)
  simp [this]

theorem lead_pow {R C : Type} [CommRing R] [Field C] (f : R →+* C) (ξ : R) (n : ℕ) :
    Lead f ξ (ξ ^ n) n 1 := ⟨1, 1, by simp, by simp, by simp⟩

end GlobalTheory.DetInv

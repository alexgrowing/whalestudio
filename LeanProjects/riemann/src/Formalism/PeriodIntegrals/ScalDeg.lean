import Mathlib

noncomputable section

namespace PI.ScalDeg

abbrev FrV (T : Type) (N : ℕ) : Type := T × Fin N × Fin N

abbrev Idx (T : Type) (N N' : ℕ) : Type := T × Fin N' × Fin N

def polD {T : Type} {N N' : ℕ} (s : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) : MvPolynomial (Idx T N N') ℂ :=
  MvPolynomial.aeval (fun k : FrV T N => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx T N N')) Q

def sclP {T : Type} {N N' : ℕ} (s : T → ℂ) (P : MvPolynomial (Idx T N N') ℂ) : MvPolynomial (Idx T N N') ℂ :=
  MvPolynomial.aeval (fun k : Idx T N N' => MvPolynomial.C (s k.1) * MvPolynomial.X k) P

open Classical in

def HomDeg {T : Type} {N : ℕ} (Qp : MvPolynomial (FrV T N) ℂ) (dg : T → ℕ) : Prop :=
  ∀ α ∈ Qp.support, ∀ τ, (α.sum fun k n => if k.1 = τ then n else 0) = dg τ

def ScalDeg : Prop :=
  ∀ (T : Type) [Fintype T] (N N' : ℕ) (s s' : T → ℂ) (Qp : MvPolynomial (FrV T N) ℂ) (dg : T → ℕ), HomDeg Qp dg →
    ∀ (y' : T → Matrix (Fin N') (Fin N') ℂ),
      polD (fun τ => s τ * s' τ) Qp y' = MvPolynomial.C (∏ τ, s τ ^ dg τ) * polD s' Qp y' ∧
      sclP s (polD s' Qp y') = polD (fun τ => s τ * s' τ) Qp y'

end PI.ScalDeg

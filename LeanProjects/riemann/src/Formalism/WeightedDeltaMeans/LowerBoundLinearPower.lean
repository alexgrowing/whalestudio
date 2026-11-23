import Mathlib

open Finset MvPolynomial Filter Topology

noncomputable section

namespace Formalism.ShimuraLimitIdentity

abbrev Pol (Ψ : Type) (N : ℕ) := MvPolynomial (Ψ × Fin N) ℝ

def top (N j : ℕ) : Finset (Fin N) := univ.filter (fun i : Fin N => i.val < j)

def psumAt {Ψ : Type} {N : ℕ} (τ : Ψ) (k : ℕ) : Pol Ψ N := ∑ i : Fin N, X (τ, i) ^ k

def psumTop {Ψ : Type} {N : ℕ} (j : ℕ) (τ : Ψ) (k : ℕ) : Pol Ψ N := ∑ i ∈ top N j, X (τ, i) ^ k

def Sh {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) (j : ℕ) (τ : Ψ) (F : Pol Ψ N) : ℝ :=
  I (∑ i ∈ top N j, pderiv (τ, i) F)

def Tot {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) (τ : Ψ) (F : Pol Ψ N) : ℝ :=
  I (∑ i : Fin N, pderiv (τ, i) F)

def lin {Ψ : Type} [Fintype Ψ] {N : ℕ} (u : Ψ → Fin N → ℝ) : Pol Ψ N :=
  -(∑ τ : Ψ, ∑ i : Fin N, C (u τ i) * X (τ, i))

def Kills {Ψ : Type} {N : ℕ} (I : Pol Ψ N →ₗ[ℝ] ℝ) : Prop :=
  ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → ∀ G : Pol Ψ N, I (psumAt τ k * G) = 0

def ShTotDecomp : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j K : ℕ) (I : Pol Ψ N →ₗ[ℝ] ℝ), Kills I → 1 ≤ K →
    ∀ (Q : Ψ → ℕ → Pol Ψ N) (τ : Ψ),
      Sh I j τ (∑ σ : Ψ, ∑ k ∈ Icc 1 K, psumAt σ k * Q σ k)
          = (∑ k ∈ Icc 1 K, (k : ℝ) * I (psumTop j τ (k - 1) * Q τ k)) ∧
      Tot I τ (∑ σ : Ψ, ∑ k ∈ Icc 1 K, psumAt σ k * Q σ k) = (N : ℝ) * I (Q τ 1)

def ShTotPower : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j D : ℕ) (I : Pol Ψ N →ₗ[ℝ] ℝ)
    (u : Ψ → Fin N → ℝ) (τ : Ψ),
      Sh I j τ (lin u ^ (D + 1)) = -((D : ℝ) + 1) * (∑ i ∈ top N j, u τ i) * I (lin u ^ D) ∧
      Tot I τ (lin u ^ (D + 1)) = -((D : ℝ) + 1) * (∑ i : Fin N, u τ i) * I (lin u ^ D)

def TestVectors : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (I : Pol Ψ N →ₗ[ℝ] ℝ), Kills I → j ≤ N →
    ∀ (Q : Pol Ψ N) (τ σ : Ψ),
      Sh I j σ (psumAt τ 1 * Q) = (if σ = τ then (j : ℝ) * I Q else 0) ∧
      Tot I σ (psumAt τ 1 * Q) = (if σ = τ then (N : ℝ) * I Q else 0) ∧
      Sh I j σ (psumAt τ 2 * Q) = (if σ = τ then 2 * I (psumTop j τ 1 * Q) else 0) ∧
      Tot I σ (psumAt τ 2 * Q) = 0

def DeltaFunctionals : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j K : ℕ) (I : Pol Ψ N →ₗ[ℝ] ℝ), Kills I → 1 ≤ K →
    0 < N →
    ∀ (Q : Ψ → ℕ → Pol Ψ N) (F : Pol Ψ N) (geo : Ψ → ℕ → ℝ) (p vol κ δ : ℝ),
      F = (∑ σ : Ψ, ∑ k ∈ Icc 1 K, psumAt σ k * Q σ k) →
      (∀ τ, geo τ 1 = κ * I (Q τ 1)) →
      δ = Real.log p * vol *
        (∑ τ : Ψ, ∑ k ∈ Icc 1 K, (k : ℝ) * (geo τ k - I (psumTop j τ (k - 1) * Q τ k) / (p - 1))) →
      δ = -(Real.log p / (p - 1)) * vol * (∑ τ : Ψ, Sh I j τ F)
          + κ * Real.log p / (N : ℝ) * vol * (∑ τ : Ψ, Tot I τ F)
          + Real.log p * vol * (∑ τ : Ψ, ∑ k ∈ Icc 2 K, (k : ℝ) * geo τ k)

def KappaInert : Prop :=
  ∀ p r s : ℝ, 1 < p →
    (∑' n : ℕ, (p⁻¹) ^ (n + 1) * (if Even n then r else s)) = (r * p + s) / (p ^ 2 - 1)

def IdentityFiniteB : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (Pr : Finset ℕ) (NN vol hh PPB tableDegreeThreeBase EE : ℝ) (al be ShF TotF : Ψ → ℝ)
    (κ δ rest : ℕ → ℝ),
    NN ≠ 0 →
    PPB = vol * (hh - (∑ τ, (al τ - be τ) * ShF τ) - (∑ τ, be τ * TotF τ)) + EE →
    tableDegreeThreeBase = PPB + (∑ p ∈ Pr, δ p) →
    (∀ p ∈ Pr, δ p = -(Real.log p / ((p : ℝ) - 1)) * vol * (∑ τ, ShF τ)
        + κ p * Real.log p / NN * vol * (∑ τ, TotF τ) + rest p) →
    tableDegreeThreeBase = vol * (hh - (∑ τ, (al τ - be τ + (∑ p ∈ Pr, Real.log p / ((p : ℝ) - 1))) * ShF τ)
                             - (∑ τ, (be τ - (∑ p ∈ Pr, κ p * Real.log p) / NN) * TotF τ))
                           + (∑ p ∈ Pr, rest p) + EE

def LimitIdentity : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (V : Type) (ShF TotF : Ψ → V → ℝ) (PP hh rest : V → ℝ)
    (vol jj NN : ℝ) (B1 : ℕ) (a b : ℕ → Ψ → ℝ) (restB EE : ℕ → V → ℝ) (F1 F2 : Ψ → V),
    vol ≠ 0 → NN ≠ 0 →
    (∀ τ σ, ShF σ (F1 τ) = if σ = τ then jj else 0) →
    (∀ τ σ, TotF σ (F1 τ) = if σ = τ then NN else 0) →
    (∀ τ σ, ShF σ (F2 τ) = if σ = τ then 2 else 0) →
    (∀ τ σ, TotF σ (F2 τ) = 0) →
    (∀ B, B1 ≤ B → ∀ F, PP F =
      vol * (hh F - (∑ τ, a B τ * ShF τ F) - (∑ τ, b B τ * TotF τ F)) + restB B F + EE B F) →
    (∀ F, Tendsto (fun B => restB B F) atTop (𝓝 (rest F))) →
    (∀ F, Tendsto (fun B => EE B F) atTop (𝓝 0)) →
    ∃ A0 b0 : Ψ → ℝ,
      (∀ τ, Tendsto (fun B => a B τ) atTop (𝓝 (A0 τ))) ∧
      (∀ τ, Tendsto (fun B => b B τ) atTop (𝓝 (b0 τ))) ∧
      ∀ F, PP F = vol * (hh F - (∑ τ, A0 τ * ShF τ F) - (∑ τ, b0 τ * TotF τ F)) + rest F

def EvalOnPower : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j D : ℕ) (I : Pol Ψ N →ₗ[ℝ] ℝ)
    (u : Ψ → Fin N → ℝ) (A0 b0 : Ψ → ℝ) (vol hhF restF PPF : ℝ),
    PPF = vol * (hhF - (∑ τ, A0 τ * Sh I j τ (lin u ^ (D + 1)))
            - (∑ τ, b0 τ * Tot I τ (lin u ^ (D + 1)))) + restF →
    PPF = vol * hhF + ((D : ℝ) + 1) * (vol * I (lin u ^ D)) *
        (∑ τ, (A0 τ * (∑ i ∈ top N j, u τ i) + b0 τ * (∑ i : Fin N, u τ i))) + restF

def LowerBoundLinearPower : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j D : ℕ) (I : Pol Ψ N →ₗ[ℝ] ℝ), Kills I → 0 < N →
    j ≤ N →
    ∀ (PP hh rest : Pol Ψ N → ℝ) (vol : ℝ) (A0 b0 : Ψ → ℝ), 0 < vol →

    (∀ F : Pol Ψ N, F.IsHomogeneous (D + 1) →
      PP F = vol * (hh F - (∑ τ, A0 τ * Sh I j τ F) - (∑ τ, b0 τ * Tot I τ F)) + rest F) →
    ∀ (u : Ψ → Fin N → ℝ), (∀ τ, Antitone (u τ)) → 0 < I (lin u ^ D) →
    ∀ (Q Q2 : Pol Ψ N) (Λ K1 K2 K5 spread : ℝ), 1 ≤ D → Q.IsHomogeneous D →
    Q2.IsHomogeneous (D - 1) → 0 ≤ Λ → 0 ≤ K1 → 0 ≤ K2 →

    0 ≤ hh (lin u ^ (D + 1)) →

    I Q = 1 → (∀ τ, hh (psumAt τ 1 * Q) = 0) → (∀ τ, rest (psumAt τ 1 * Q) = 0) →
    (∀ τ, |PP (psumAt τ 1 * Q)| ≤ vol * (K1 * N * Λ)) →

    (∀ τ σ, A0 τ = A0 σ) →
    (∑ τ, I (psumTop j τ 1 * Q2)) ≠ 0 →
    -(K2 * Λ) ≤ (hh (∑ τ, psumAt τ 2 * Q2) - PP (∑ τ, psumAt τ 2 * Q2) / vol
        + rest (∑ τ, psumAt τ 2 * Q2) / vol) / (2 * (∑ τ, I (psumTop j τ 1 * Q2))) →

    |rest (lin u ^ (D + 1))| ≤ K5 * (((D : ℝ) + 1) * (vol * I (lin u ^ D)) * spread) →
    -(((D : ℝ) + 1) * (vol * I (lin u ^ D)) *
        ((K1 + K2) * Λ * (∑ τ, ∑ i, |u τ i|) + K5 * spread)) ≤ PP (lin u ^ (D + 1))

end Formalism.ShimuraLimitIdentity

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TauZero
import Formalism.HermitianCurvature.StatementTBB

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BpJoin

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData BranchingSupport

def Pst {n : ℕ} (lam : Fin n → ℝ) (c : ℝ) (y : ℝ) : ℝ := ∏ s, (|y + lam s| + c)

def GridNum (C b c : ℝ) (P : M.Par) (l : ℕ) (lam : Fin (2 * P.r + P.k + 1) → ℝ) : Prop :=
  1 ≤ c ∧ c + 2 ≤ b ∧ (P.k : ℝ) ≤ b ∧ |P.u l| ≤ b ∧ |P.u' l| ≤ b ∧ (∀ s, |lam s| ≤ b) ∧
  (∀ s t, s < t → lam t + 2 * c ≤ lam s) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u (s.val + 2) + 1 / 2 ≤ lam s)) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u' (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u' (s.val + 2) + 1 / 2 ≤ lam s)) ∧
  b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T ∧ b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T'

def StdNum (C b c : ℝ) (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) : Prop :=
  (∀ l ∈ Icc 1 P.k, GridNum C b c P l lam) ∧
  (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k →
    lam s + 1 / 2 ≤ P.u (s.val + 1) ∧ P.u (s.val + 2) + 1 / 2 ≤ lam s ∧
    lam s + 1 / 2 ≤ P.u' (s.val + 1) ∧ P.u' (s.val + 2) + 1 / 2 ≤ lam s)

def Cases (P : M.Par) (n₀ : ℕ) : Prop :=
  (n₀ = 0 ∧ ∃ l ∈ Icc 1 P.k, ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u l - P.u' l|) ∨
  (n₀ = 30 * (P.r + 1) ^ 2 + 6 ∧ (∀ i ∈ Icc 1 P.k, P.u i = P.u' i) ∧
    ∃ l, 1 ≤ l ∧ l < P.k ∧ 2 * (n₀ : ℝ) + 1 ≤ P.u' l - P.u' (l + 1))

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def EigDec {k r : ℕ} (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (mu : Fin (2 * r + k + 1) → ℝ) : Prop :=
  B.CkOn ⊤ (B.GV k r) f ∧ (∀ m : ℕ, B.InCC A m f) ∧
    ∀ y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (y : ℂ) f g = ((∏ s, (y + mu s) : ℝ) : ℂ) • f g

structure SupW (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (q0 : ℕ)
    (R : (Fin (2 * P.r + P.k + 1) → ℤ) → Rep P.k P.r) (l : ∀ ν, (R ν).H → Wp) (l' : ∀ ν, (R ν).H → Wq)
    (dg : (Fin (2 * P.r + P.k + 1) → ℤ) → ℝ) (s : (Fin (2 * P.r + P.k + 1) → ℤ) → ℂ)
    (J : (Fin (2 * P.r + P.k + 1) → ℤ) → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (tau : (Fin (2 * P.r + P.k + 1) → ℤ) → Finset (Fin (2 * P.r + P.k + 1)) → ℂ) : Prop where
  fam : IsFam lam q0 R
  left : haveI := FiniteDimensional.complete ℂ Wp
    SideFam p.T.base.z p.T.base.π p.T.base.μW p.T.base.μN p.T.base.μG q0 R l dg
  right : haveI := FiniteDimensional.complete ℂ Wq
    SideFam p.T.base.z' p.T.base.π' p.T.base.μW' p.T.base.μN p.T.base.μG q0 R l' dg
  coef : ∀ ν, n1 ν ≤ q0 → NzOn (R ν) (l ν) → NzOn (R ν) (l' ν) →
    IsCoef (R ν) (l ν) (l' ν) (J ν) (s ν) ∧ ‖s ν‖ = dg ν
  zero : ∀ ν, ¬ (n1 ν ≤ q0 ∧ NzOn (R ν) (l ν) ∧ NzOn (R ν) (l' ν)) → J ν = 0
  tau_zero : ∀ ν I, J ν = 0 ∨ J (ν + eZ I) = 0 → tau ν I = 0
  tau_eq : ∀ ν, n1 ν + (P.r + 1) * (P.r + 2) ≤ q0 →
    ∃ io pr ep, TensH (cmp (P.r + 1)) (cmp (P.r + 1) (Formalism.QuantumDeterminants.Hpk P.k P.r)) (R ν)
        (fun I : Sub (2 * P.r + P.k + 1) (P.r + 1) => R (ν + eZ I.1)) io pr ep ∧
      ∀ I : Sub (2 * P.r + P.k + 1) (P.r + 1), J ν ≠ 0 → J (ν + eZ I.1) ≠ 0 → ∃ κ κ' : ℂ,
        (∀ v ∈ (R ν).sm, l (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z)) v c)) = κ • l ν v) ∧
        (∀ v ∈ (R ν).sm, l' (ν + eZ I.1)
          (∑ c, pr I c (tm (R ν) (wedge (Formalism.QuantumDeterminants.fvec P.k P.r p.T.base.z')) v c)) = κ' • l' ν v) ∧
        tau ν I.1 = (ep I : ℂ) * κ' * star κ * s ν / s (ν + eZ I.1)

end BpJoin

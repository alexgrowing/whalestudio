import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open GlobalTheory.KZ GlobalTheory.Glue

namespace GlobalTheory.KummerEisensteinGalois

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

def IsEigenfunctionalOfL2 (X : Tower Ω ε) (A : ValuationSubring Ω) (N w : ℕ) (j : Ω →+* Qbar l) (pr : X.Fn l → Fin 2 → Qbar l)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) : Prop :=
  FinSupp lam ∧ ∃ (c : ℕ) (per : ℕ → Qbar l), (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧
    ∀ (n : ℕ), c ≤ n → ∀ (b : X.Fn l), b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ →
      Cg (n - c) (lam (seqN 1 j φ)) (per n * pr b 1)

section Induced

variable {X : Tower Ω ε} {A : ValuationSubring Ω} {N w : ℕ} {j : Ω →+* Qbar l} {pr : X.Fn l → Fin 2 → Qbar l}
  {lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l}

theorem IsEigenfunctionalOfL2.smul (h : IsEigenfunctionalOfL2 X A N w j pr lam) (a : Qbar l) : IsEigenfunctionalOfL2 X A N w j (a • pr) (a • lam) := by
  obtain ⟨hf, c, per, hper, hc⟩ := h
  obtain ⟨k, hk⟩ := exists_le_l_pow l ‖a‖
  refine ⟨hf.smul a, c + k, per, hper, fun n hn b hb φ hφ => ?_⟩
  have h1 := cg_mul_left (k := k) (m := n - c) (by omega) hk (hc n (by omega) b hb φ hφ)
  rw [Nat.sub_sub] at h1
  simpa [mul_left_comm] using h1

end Induced

end GlobalTheory.KummerEisensteinGalois

end

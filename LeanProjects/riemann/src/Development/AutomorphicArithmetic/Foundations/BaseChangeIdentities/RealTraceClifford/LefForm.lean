import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.WeylEv
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ChiInj
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SymOfMul
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem lefschetz_form_identities {A : Type*} [CommRing A] [NoZeroDivisors A]
    (D R D2 P q L T χ c₁ cT : A) (hR : R ≠ 0) (hD : D ≠ 0) (hD2 : D2 = D * R)
    (hP : P = q * (R * R)) (hχ : D * χ = L) (h1 : D2 * cT - P * T = 0)
    (h2 : D * D * c₁ - P * (L * L) = 0) :
    D * cT = q * (R * T) ∧ D * c₁ = q * (R * (D2 * (χ * χ))) := by
  subst hD2 hP hχ
  constructor
  · have h : R * (D * cT - q * (R * T)) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hR
    · linear_combination h
  · have h : D * (D * c₁ - q * (R * (D * R * (χ * χ)))) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hD
    · linear_combination h

set_option maxHeartbeats 800000 in
theorem UpperTheory.RealTr.lefForm :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (c₁ cT χ : FR n), alt (rhoV n) * χ = alt ((fun a => (lam a : ℝ)) + rhoV n) →
      (∀ (θ : Wt n) (z : Fin n → ℂ), (∀ a, z a = Complex.exp (Complex.I * θ a)) → (Function.Injective fun a => z a ^ 2) →
        evT θ c₁ = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam z ^ 2 ∧
        evT θ cT = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam fun a => z a ^ 2) →
      alt (rhoV n) * cT = (2 : ℂ) ^ n • (chR n * alt (twoL lam)) ∧
        alt (rhoV n) * c₁ = (2 : ℂ) ^ n • (chR n * (alt ((2 : ℝ) • rhoV n) * (χ * χ))) := by
  intro n lam c₁ cT χ hχ hev
  obtain ⟨hD2, hD, hR, -, -, -, hP, -⟩ := chRF n
  have hP' : (∏ a, ∏ b, (1 + ex (rt a b)) : FR n) = ((2:ℂ) ^ n • (1 : FR n)) * (chR n * chR n) := by
    rw [hP, smul_mul_assoc, one_mul]
  have h1 : alt ((2:ℝ) • rhoV n) * cT - (∏ a, ∏ b, (1 + ex (rt a b))) * alt (twoL lam) = 0 := by
    apply evInj
    intro θ hinj
    obtain ⟨-, hw2, hw3, -⟩ := weylEv n lam θ (fun a => Complex.exp (Complex.I * θ a)) (fun a => rfl)
    obtain ⟨-, hc⟩ := hev θ (fun a => Complex.exp (Complex.I * θ a)) (fun a => rfl) hinj
    rw [map_sub, map_mul, map_mul, hc, ← hw2 hinj, ← hw3, sub_eq_zero, mul_comm, mul_assoc]
  have h2 : alt (rhoV n) * alt (rhoV n) * c₁ - (∏ a, ∏ b, (1 + ex (rt a b)))
      * (alt ((fun a => (lam a : ℝ)) + rhoV n) * alt ((fun a => (lam a : ℝ)) + rhoV n)) = 0 := by
    apply evInj
    intro θ hinj
    have hz : Function.Injective (fun a => Complex.exp (Complex.I * θ a)) :=
      fun a b h => hinj (by simp only [h])
    obtain ⟨hw1, -, hw3, -⟩ := weylEv n lam θ (fun a => Complex.exp (Complex.I * θ a)) (fun a => rfl)
    obtain ⟨hc, -⟩ := hev θ (fun a => Complex.exp (Complex.I * θ a)) (fun a => rfl) hinj
    rw [map_sub, map_mul, map_mul, map_mul, map_mul, hc, ← hw1 hz, ← hw3]
    generalize (evT θ) (alt (rhoV n)) = A
    generalize (∏ a, ∏ b, (1 + Complex.exp (Complex.I * θ a) / Complex.exp (Complex.I * θ b))) = B
    generalize weylChar lam (fun a => Complex.exp (Complex.I * θ a)) = W
    ring
  obtain ⟨k1, k2⟩ := lefschetz_form_identities (alt (rhoV n)) (chR n) (alt ((2:ℝ) • rhoV n))
    (∏ a, ∏ b, (1 + ex (rt a b))) ((2:ℂ) ^ n • (1 : FR n))
    (alt ((fun a => (lam a : ℝ)) + rhoV n)) (alt (twoL lam)) χ c₁ cT hR hD hD2 hP' hχ h1 h2
  refine ⟨?_, ?_⟩
  · rw [k1, smul_mul_assoc, one_mul]
  · rw [k2, smul_mul_assoc, one_mul]

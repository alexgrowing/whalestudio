import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RankinTorusVanishing

open Ad3 Ad3.R

section Mat

variable {R : Type*} [CommRing R]

theorem diagonal_mul_unipotent (a : Rˣ) (y : R) :
    (dg2 a 1 * uni2 y : GL (Fin 2) R) = uni2 ((a : R) * y) * dg2 a 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, uni2, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagonal_mul_diagonal_alt (a b c d : Rˣ) :
    (dg2 a b * dg2 c d : GL (Fin 2) R) = dg2 (a * c) (b * d) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem scalar_diagonal_one_one : (dg2 1 1 : GL (Fin 2) R) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg2]

end Mat

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unipotent_integral_mem_compact {y : F} (hy : y ∈ 𝒪[F]) : uni2 y ∈ integralGL F 2 := by
  rw [GLnLocal.mem_integralGL_iff]
  have hn : -y ∈ 𝒪[F] := neg_mem hy
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [uni2, hy, hn, zero_mem, one_mem]

theorem mem_of_ord_nonneg {a : Fˣ} (h : 0 ≤ ord (a : F)) : (a : F) ∈ 𝒪[F] :=
  mem_valBall_zero_iff.1 ((mem_valBall_iff_le_ord a.ne_zero).2 h)

theorem scalar_diagonal_mem_level_zero {u : Fˣ} (hu : ord (u : F) = 0) : dg2 u 1 ∈ integralGL F 2 := by
  rw [GLnLocal.mem_integralGL_iff]
  have h1 : (u : F) ∈ 𝒪[F] := mem_of_ord_nonneg hu.ge
  have h2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := mem_of_ord_nonneg (by rw [ord_units_inv, hu]; simp)
  have h2' : (u : F)⁻¹ ∈ 𝒪[F] := by simpa using h2
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;>
    simp [dg2, h1, h2', zero_mem, one_mem]

theorem exists_iwasawa2 (g : GL (Fin 2) F) :
    ∃ (x : F) (a d : Fˣ), ∃ k ∈ integralGL F 2, g = uni2 x * dg2 a d * k := by
  obtain ⟨b, hb, k, hk, rfl⟩ := Iwasawa.exists_borel_mul_integralGL F 2 g
  have h10 : b 1 0 = 0 := hb (by simp)
  have h0 : b 0 0 ≠ 0 := Iwasawa.apply_self_ne_zero_of_mem_borel F 2 hb 0
  have h1 : b 1 1 ≠ 0 := Iwasawa.apply_self_ne_zero_of_mem_borel F 2 hb 1
  refine ⟨b 0 1 / b 1 1, Units.mk0 _ h0, Units.mk0 _ h1, k, hk, ?_⟩
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg2, uni2, Matrix.mul_apply, Fin.sum_univ_two, h10, h1]

end Loc

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  {ψ : AddChar F Circle} {ω : Fˣ →* ℂˣ} {lam : ℂ} {W : GL (Fin 2) F → ℂ}

theorem psi_integral (hψ : IsStd ψ) {x : F} (hx : x ∈ 𝒪[F]) : ψ x = 1 := by
  have h := isTrivialOn_addCharConductor hψ.1 hψ.2.1
  rw [hψ.2.2] at h
  exact h x (mem_valBall_zero_iff.2 hx)

theorem torus_mul_unit (hT : TypeT lam W) (a : Fˣ) {u : Fˣ} (hu : ord (u : F) = 0) :
    W (dg2 (a * u) 1) = W (dg2 a 1) := by
  have h : (dg2 (a * u) 1 : GL (Fin 2) F) = dg2 a 1 * dg2 u 1 := by
    rw [diagonal_mul_diagonal_alt, one_mul]
  rw [h, hT.1 _ (scalar_diagonal_mem_level_zero hu)]

theorem torus_eq_zero_of_ord_neg (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeT lam W) {a : Fˣ}
    (ha : ord (a : F) < 0) : W (dg2 a 1) = 0 := by
  have hnt := not_isTrivialOn_addCharConductor_sub_one hψ.1 hψ.2.1
  rw [hψ.2.2] at hnt
  simp only [IsTrivialOn, not_forall] at hnt
  obtain ⟨x, hx, hne⟩ := hnt
  have hx' : x ∈ valBall F (ord (a : F)) := valBall_antitone (by omega) hx
  obtain ⟨y, rfl⟩ := exists_mul_of_mem_valBall a.ne_zero hx'
  have h1 := hT.1 (uni2 (y : F)) (unipotent_integral_mem_compact y.2) (dg2 a 1)
  rw [diagonal_mul_unipotent, hL.1] at h1
  have h2 : ((ψ ((a : F) * y) : ℂ) - 1) * W (dg2 a 1) = 0 := by
    rw [sub_mul, h1]; ring
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (Circle.coe_eq_one.1 (sub_eq_zero.1 h)) hne
  · exact h

theorem torus_hecke (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeT lam W) {ϖ : Fˣ} {B : Finset F}
    (hR : Reps ϖ B) {a : Fˣ} (ha : 0 ≤ ord (a : F)) :
    (B.card : ℂ) * W (dg2 (a * ϖ) 1) + ((ω ϖ : ℂˣ) : ℂ) * W (dg2 (a * ϖ⁻¹) 1) =
      lam * W (dg2 a 1) := by
  have h := hT.2 ϖ B hR (dg2 a 1)
  have h1 : ∀ b ∈ B, W (dg2 a 1 * upm ϖ b) = W (dg2 (a * ϖ) 1) := by
    intro b hb
    have hab : (a : F) * b ∈ 𝒪[F] := mul_mem (mem_of_ord_nonneg ha) (hR.2.1 b hb)
    rw [upm, ← mul_assoc, diagonal_mul_unipotent, mul_assoc, diagonal_mul_diagonal_alt, hL.1, psi_integral hψ hab]
    simp
  have h2 : W (dg2 a 1 * dg2 1 ϖ) = ((ω ϖ : ℂˣ) : ℂ) * W (dg2 (a * ϖ⁻¹) 1) := by
    have h3 : (dg2 a 1 * dg2 1 ϖ : GL (Fin 2) F) = dg2 ϖ ϖ * dg2 (a * ϖ⁻¹) 1 := by
      rw [diagonal_mul_diagonal_alt, diagonal_mul_diagonal_alt, mul_one, one_mul, mul_one, mul_left_comm, mul_inv_cancel,
        mul_one]
    rw [h3, hL.2]
  rw [Finset.sum_congr rfl h1, h2] at h
  simpa [Finset.sum_const, nsmul_eq_mul] using h

theorem card_ne_zero {ϖ : Fˣ} {B : Finset F} (hR : Reps ϖ B) : (B.card : ℂ) ≠ 0 := by
  obtain ⟨b, ⟨hb, -⟩, -⟩ := hR.2.2 0 (zero_mem _)
  exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem hb)

theorem torus_pow_eq_zero (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeT lam W) {ϖ : Fˣ}
    {B : Finset F} (hR : Reps ϖ B) (h1 : W 1 = 0) (n : ℕ) :
    W (dg2 (ϖ ^ (n : ℤ)) 1) = 0 ∧ W (dg2 (ϖ ^ ((n : ℤ) - 1)) 1) = 0 := by
  induction n with
  | zero =>
    refine ⟨by simpa [scalar_diagonal_one_one] using h1, torus_eq_zero_of_ord_neg hψ hL hT ?_⟩
    rw [ord_units_zpow, hR.1]
    simp
  | succ n ih =>
    have hn : 0 ≤ ord ((ϖ ^ (n : ℤ) : Fˣ) : F) := by
      rw [ord_units_zpow, hR.1]
      simp
    have h := torus_hecke hψ hL hT hR hn
    rw [← _root_.zpow_add_one, ← _root_.zpow_sub_one, ih.1, ih.2, mul_zero, mul_zero, add_zero] at h
    push_cast
    refine ⟨(mul_eq_zero.1 h).resolve_left (card_ne_zero hR), ?_⟩
    simpa using ih.1

theorem torus_eq_zero (hψ : IsStd ψ) (hL : Law ψ ω W) (hT : TypeT lam W) {ϖ : Fˣ}
    {B : Finset F} (hR : Reps ϖ B) (h1 : W 1 = 0) (a : Fˣ) : W (dg2 a 1) = 0 := by
  by_cases h : ord (a : F) < 0
  · exact torus_eq_zero_of_ord_neg hψ hL hT h
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 h)
  have hu : ord ((a * (ϖ ^ (n : ℤ))⁻¹ : Fˣ) : F) = 0 := by
    rw [ord_units_mul, ord_units_inv, ord_units_zpow, hR.1, hn]
    simp
  have ha : a = ϖ ^ (n : ℤ) * (a * (ϖ ^ (n : ℤ))⁻¹) := by
    rw [mul_left_comm, mul_inv_cancel, mul_one]
  rw [ha, torus_mul_unit hT _ hu]
  exact (torus_pow_eq_zero hψ hL hT hR h1 n).1

end Main

theorem spherical_whittaker_eq_zero : Ad3.R.C1 → Ad3.R.U0 := by
  intro hC F _ _ _ _ _ _ ψ hψ ω lam W hL hT h1
  obtain ⟨⟨ϖ, B, hR⟩, -, -⟩ := hC F ψ hψ
  funext g
  obtain ⟨x, a, d, k, hk, rfl⟩ := exists_iwasawa2 g
  have h : (dg2 a d : GL (Fin 2) F) = dg2 d d * dg2 (a * d⁻¹) 1 := by
    rw [diagonal_mul_diagonal_alt, mul_one, mul_left_comm, mul_inv_cancel, mul_one]
  rw [hT.1 k hk, hL.1, h, hL.2, torus_eq_zero hψ hL hT hR h1]
  simp

end GlobalTheory.CompanionTheory.RankinTorusVanishing

end

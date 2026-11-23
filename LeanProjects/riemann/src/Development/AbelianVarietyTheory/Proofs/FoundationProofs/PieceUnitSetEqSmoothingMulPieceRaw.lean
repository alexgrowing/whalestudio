import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.Smoothing

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem zpow_congr_of_pow_eq_one {ζ : K} {M : ℕ} (hM : 0 < M) (hζ : ζ ^ M = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD M]) : ζ ^ a = ζ ^ b := by
  have hz : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨s, hs⟩ := h.dvd
  have hb : b = a + M * s := by linarith
  rw [hb, zpow_add₀ hz, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

theorem eisF_congr_mod {j M : ℕ} (hM : 0 < M) {ζ : K} (hζ : ζ ^ M = 1) {a₁ a₂ b₁ b₂ : ℤ}
    (h₁ : a₁ ≡ b₁ [ZMOD M]) (h₂ : a₂ ≡ b₂ [ZMOD M]) :
    eisF j M ζ a₁ a₂ = eisF j M ζ b₁ b₂ := by
  funext n
  have h₁' : a₁ % (M : ℤ) = b₁ % (M : ℤ) := h₁
  have hc : const0 j M ζ a₁ a₂ = const0 j M ζ b₁ b₂ := by
    have hd : ((M : ℤ) ∣ a₁) ↔ ((M : ℤ) ∣ b₁) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, h₁']
    have hf : frc M a₁ = frc M b₁ := by unfold frc; rw [h₁']
    unfold const0
    rw [zpow_congr_of_pow_eq_one hM hζ h₂, hf]
    simp only [hd]
  have hp : coefPos j M ζ a₁ a₂ n = coefPos j M ζ b₁ b₂ n := by
    unfold coefPos
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have e1 : ∀ z : ℤ, z ≡ a₁ [ZMOD M] ↔ z ≡ b₁ [ZMOD M] :=
      fun z => ⟨fun h => h.trans h₁, fun h => h.trans h₁.symm⟩
    rw [zpow_congr_of_pow_eq_one hM hζ (h₂.mul_right (d : ℤ)),
      zpow_congr_of_pow_eq_one hM hζ (h₂.mul_right (d : ℤ)).neg]
    simp only [e1]
  unfold eisF
  rw [hc, hp]

omit [CharZero K] in
theorem cmul_expand (a b a' b' : K) (f g h l : ℕ → K) (r : ℕ) :
    cmul (fun i => a * f i - b * g i) (fun i => a' * h i - b' * l i) r =
      a * a' * cmul f h r - a * b' * cmul f l r - b * a' * cmul g h r + b * b' * cmul g l r := by
  unfold cmul
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem not_dvd_val_iff_isUnit {p n : ℕ} [hp : Fact p.Prime] (hn : 0 < n) (y : ZMod (p ^ n)) :
    ¬ p ∣ y.val ↔ IsUnit y := by
  have h := ZMod.isUnit_iff_coprime y.val (p ^ n)
  rw [ZMod.natCast_zmod_val] at h
  rw [h, Nat.coprime_pow_right_iff hn, Nat.coprime_comm, hp.out.coprime_iff_not_dvd]

theorem isUnit_intCast_of_not_dvd {p n : ℕ} [hp : Fact p.Prime] {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) : IsUnit (c : ZMod (p ^ n)) := by
  have h1 : IsCoprime (p : ℤ) c :=
    (Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr hc
  obtain ⟨a, b, hab⟩ := (h1.pow_left (m := n))
  have h2 : ((a * (p : ℤ) ^ n + b * c : ℤ) : ZMod (p ^ n)) = 1 := by rw [hab]; simp
  have h3 : ((p : ZMod (p ^ n))) ^ n = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  push_cast at h2
  rw [h3, mul_zero, zero_add, mul_comm] at h2
  exact IsUnit.of_mul_eq_one _ h2

def diagGL {R : Type*} [CommRing R] (u v : Rˣ) : GL (Fin 2) R :=
  ⟨Matrix.diagonal ![(u : R), v], Matrix.diagonal ![((u⁻¹ : Rˣ) : R), ((v⁻¹ : Rˣ) : R)],
   by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp,
   by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp⟩

theorem diagGL_mul_zero {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) (j : Fin 2) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 j =
      (u : R) * (γ : Matrix (Fin 2) (Fin 2) R) 0 j := by
  rw [Units.val_mul]
  exact Matrix.diagonal_mul _ _ _ _

theorem diagGL_mul_one {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) (j : Fin 2) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 j =
      (v : R) * (γ : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul]
  exact Matrix.diagonal_mul _ _ _ _

theorem diagGL_mul_det {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det =
      (u : R) * v * (γ : Matrix (Fin 2) (Fin 2) R).det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [diagGL_mul_zero, diagGL_mul_one]
  ring

theorem diagGL_mul_mem {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (u v : (ZMod (p ^ n))ˣ)
    (γ : GL (Fin 2) (ZMod (p ^ n))) : diagGL u v * γ ∈ unitSet p n ↔ γ ∈ unitSet p n := by
  simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, not_dvd_val_iff_isUnit hn,
    diagGL_mul_zero, diagGL_mul_one, Units.isUnit_units_mul]

end GlobalTheory.KummerEisensteinGalois.Smoothing

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory

theorem nat_le_four_of_dvd_of_embeddings_le_four :
    ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ) (r : 𝓞 F), y ≠ 0 → y = m * r →
    (∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4) → m ≤ 4 := by
  intro F _ _ y m r hy hyr hφ
  set d := Module.finrank ℚ F with hd
  have hr : (r : F) ≠ 0 := by rintro h; apply hy; rw [hyr, h, mul_zero]
  have hm : (m : F) ≠ 0 := by rintro h; apply hy; rw [hyr, h, zero_mul]
  have hN : Algebra.norm ℚ y = (m : ℚ) ^ d * (Algebra.norm ℤ r : ℚ) := by
    rw [hyr, map_mul, Algebra.coe_norm_int]
    congr 1
    rw [show ((m : F)) = algebraMap ℚ F (m : ℚ) by simp, Algebra.norm_algebraMap]
  have hr0 : (Algebra.norm ℤ r : ℚ) ≠ 0 := by
    rw [Algebra.coe_norm_int]; exact (Algebra.norm_ne_zero_iff).2 hr
  have hr1 : (1 : ℝ) ≤ |((Algebra.norm ℤ r : ℤ) : ℝ)| := by
    have : Algebra.norm ℤ r ≠ 0 := by exact_mod_cast hr0
    exact_mod_cast Int.one_le_abs this
  have hlow : (m : ℝ) ^ d ≤ |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
    rw [hN]; push_cast
    rw [abs_mul, abs_pow, Nat.abs_cast]
    nlinarith [pow_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) d]
  have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  have hup : |((Algebra.norm ℚ y : ℚ) : ℝ)| ≤ 4 ^ d := by
    have h1 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ y)‖ = |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
      simp
    rw [← h1, hprod, norm_prod]
    calc ∏ σ : F →ₐ[ℚ] ℂ, ‖σ y‖ ≤ ∏ _σ : F →ₐ[ℚ] ℂ, (4 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun σ _ => hφ σ.toRingHom)
      _ = 4 ^ d := by rw [Finset.prod_const, Finset.card_univ, AlgHom.card]
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have : (m : ℝ) ≤ 4 := (pow_le_pow_iff_left₀ (Nat.cast_nonneg m) (by norm_num) hd0).1 (hlow.trans hup)
  exact_mod_cast this

end GlobalTheory

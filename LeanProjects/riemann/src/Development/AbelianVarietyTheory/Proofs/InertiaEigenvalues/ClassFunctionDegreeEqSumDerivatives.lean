import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicClassFunBlockDiagonalEqSumDerivatives
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GgOneAndIsClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.DegDer

variable {g : ℕ} [Fact g.Prime]

theorem tl_one {a n : ℕ} (h : a ≤ n) : tl a (1 : Mt g n) = (1 : Mt g a) := by
  ext i j
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]

theorem br_one {a b n : ℕ} (h : a + b ≤ n) : br a b (1 : Mt g n) = (1 : Mt g b) := by
  ext i j
  have hi : a + (i : ℕ) < n := by omega
  have hj : a + (j : ℕ) < n := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]
  simp

theorem toG_one {n : ℕ} : toG (1 : Mt g n) = 1 := by
  unfold toG
  rw [dif_pos isUnit_one]
  ext : 1
  simp

theorem hc_one (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 = ((Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) : ℕ) : ℂ)⁻¹ *
      ((Fintype.card (Gn g (a + b)) : ℂ) * (α 1 * β 1)) := by
  unfold hc hcT
  rw [← GlobalTheory.GLm.ParBasic.card_par]
  congr 1
  simp only [mul_one, inv_mul_cancel, Units.val_one, GlobalTheory.GLm.ParBasic.inPar_one, if_true,
    tl_one (Nat.le_add_right a b), br_one (le_refl (a + b)), toG_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

theorem blockDiagonalWithIdentityGL_one (k : ℕ) : diag1 (1 : Gn g k) (k + 1) = 1 := by
  unfold diag1
  have : (fun i j : Fin (k + 1) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN ((1 : Gn g k) : Mt g k) i j
      else (1 : Mt g (k + 1)) i j) = (1 : Mt g (k + 1)) := by
    ext i j
    split_ifs with h
    · simp only [Units.val_one, entN, h, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]
    · rfl
  rw [this, toG_one]

theorem prod_pow_add (a b : ℕ) :
    (∏ i : Fin (a + b), (g : ℂ) ^ (i : ℕ)) =
      (∏ i : Fin a, (g : ℂ) ^ (i : ℕ)) * (∏ i : Fin b, (g : ℂ) ^ (i : ℕ)) * (g : ℂ) ^ (a * b) := by
  rw [Fin.prod_univ_add]
  simp only [Fin.coe_castAdd, Fin.coe_natAdd, pow_add, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]
  ring

theorem prod_Icc_add (f : ℕ → ℂ) (a b : ℕ) :
    (∏ i ∈ Finset.Icc 1 (a + b), f i) = (∏ i ∈ Finset.Icc 1 a, f i) * ∏ i ∈ Finset.Ico (a + 1) (a + b + 1), f i := by
  have e : ∀ n, Finset.Icc 1 n = Finset.Ico 1 (n + 1) := fun n => by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e, e, Finset.prod_Ico_consecutive _ (by omega) (by omega)]

theorem card_Gn_factors_ne_zero (n : ℕ) :
    (∏ i : Fin n, (g : ℂ) ^ (i : ℕ)) ≠ 0 ∧ (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) ≠ 0 := by
  have h : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [GlobalTheory.GLq.GGDeg.card_Gn] at h
  exact mul_ne_zero_iff.mp h

theorem one_eq_sum_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (χ : Gn g n → ℂ),
    0 < n → IsClass χ → χ 1 = ∑ m ∈ Finset.range n, der ψ m χ 1 * ∏ i ∈ Finset.Ico (m + 1) n, ((g : ℂ) ^ i - 1) := by
  intro g _ ψ hψ n χ hn hχ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hM : IsMirClass χ := fun p x _ _ => hχ x p
  have h1 : χ 1 = χ (diag1 (1 : Gn g k) (k + 1)) := by rw [blockDiagonalWithIdentityGL_one]
  rw [h1, GlobalTheory.GLm.mirClass_diag1_eq_sum g ψ hψ k χ hM 1]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
  obtain ⟨b, rfl⟩ : ∃ b, k = i + b := ⟨k - i, by omega⟩
  have hkb : i + b - i = b := by omega
  rw [hkb, hc_one, (GlobalTheory.GLq.GGDeg.gg_one_and_isClass g ψ b).1]
  push_cast
  rw [GlobalTheory.GLq.GGDeg.card_Gn i, GlobalTheory.GLq.GGDeg.card_Gn b, GlobalTheory.GLq.GGDeg.card_Gn (i + b), prod_pow_add,
    prod_Icc_add]
  obtain ⟨hPi, hQi⟩ := card_Gn_factors_ne_zero (g := g) i
  obtain ⟨hPb, hQb⟩ := card_Gn_factors_ne_zero (g := g) b
  have hg : (g : ℂ) ^ (i * b) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero)
  field_simp

end GlobalTheory.GLq.DegDer

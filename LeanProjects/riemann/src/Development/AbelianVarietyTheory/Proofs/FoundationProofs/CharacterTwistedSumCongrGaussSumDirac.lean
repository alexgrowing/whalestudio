import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPrimCharMulRootPowModPow

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

noncomputable section

namespace GlobalTheory.KZ.Cmp.ChD

variable {l : ℕ} [Fact l.Prime]

theorem sum_units_eq_sum {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (f : ZMod N → Qbar l) :
    ∑ b : (ZMod N)ˣ, ψ b * f b = ∑ a : ZMod N, ψ a * f a := by
  refine Fintype.sum_of_injective (fun b : (ZMod N)ˣ => (b : ZMod N)) Units.val_injective _ _ ?_ (fun b => rfl)
  intro a ha
  have : ¬ IsUnit a := fun hu => ha ⟨hu.unit, rfl⟩
  rw [MulChar.map_nonunit ψ this, zero_mul]

theorem norm_apply_unit_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (b : (ZMod N)ˣ) :
    ‖ψ b‖ ≤ 1 := by
  have h : (ψ b) ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h1 := congrArg norm h
  rw [norm_pow, norm_one] at h1
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h1).le

theorem sum_units_char_pow (m : ℕ) (hm : 1 ≤ m) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m))
    (hz : IsPrimitiveRoot z (l ^ m)) (hψ : ψ.IsPrimitive) (j : ℕ) :
    ∑ b : (ZMod (l ^ m))ˣ, ψ b * (z ^ (b : ZMod (l ^ m)).val) ^ j = ψ⁻¹ (j : ZMod (l ^ m)) * gSum m z ψ := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have key := GlobalTheory.EisM.sum_primChar_mul_rootPow_mod_pow (Qbar l) l m m z ψ (Fact.out) hm le_rfl hz hψ (j : ℤ)
  simp only [Nat.sub_self, pow_zero, one_dvd, if_true, one_mul, Int.ediv_one, Int.cast_natCast] at key
  rw [sum_units_eq_sum ψ (fun a => (z ^ a.val) ^ j)]
  unfold gSum
  rw [sum_units_eq_sum ψ (fun a => z ^ a.val)]
  have e1 : ∑ a : ZMod (l ^ m), ψ a * (z ^ a.val) ^ j =
      ∑ r : ZMod (l ^ m), ψ ((r.val : ℕ) : ZMod (l ^ m)) * z ^ ((r.val : ℤ) * (j : ℤ)) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ZMod.natCast_zmod_val, ← Nat.cast_mul, zpow_natCast, pow_mul]
  rw [e1, key, mul_comm]

theorem chSum_gauss : ∀ (l : ℕ) [Fact l.Prime] (F : PowerSeries (Qbar l)) (a : ℕ → Qbar l) (N m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), 1 ≤ m → l ^ (3 * m) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → Cg (2 * m) (chSum F m z ψ) (gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m))) := by
  intro l _ F a N m z ψ hm hN hF htv hz hψ
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hex : gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m)) =
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval F N (z ^ (b : ZMod (l ^ m)).val) := by
    simp_rw [htv, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : ∑ b : (ZMod (l ^ m))ˣ, ψ b * (a j * (z ^ (b : ZMod (l ^ m)).val) ^ j) =
        a j * ∑ b : (ZMod (l ^ m))ˣ, ψ b * (z ^ (b : ZMod (l ^ m)).val) ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e, sum_units_char_pow m hm z ψ hz hψ j]
    ring
  unfold Cg
  rw [hex]
  unfold chSum
  rw [← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_apply_unit_le_one ψ b)).trans ?_
  have hy : (z ^ (b : ZMod (l ^ m)).val) ^ (l ^ m) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  have hy1 := GlobalTheory.AmiceDist.norm_sub_one_le hy
  have hy3 := GlobalTheory.AmiceDist.norm_sub_one_pow_three_le hy
  unfold tval
  rw [← Finset.sum_range_add_sum_Ico _ hN, sub_add_cancel_left, norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n hn => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (hF n)).trans
    ((pow_le_pow_of_le_one (norm_nonneg _) hy1 (Finset.mem_Ico.1 hn).1).trans hy3)

end GlobalTheory.KZ.Cmp.ChD

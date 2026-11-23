import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.StatementE
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexEqOfSurj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipLatIsOpenIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerTail

open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal

noncomputable section
namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

abbrev upPairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2

theorem relIndex_unipLat {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c C : Fin n → Fin n → ℤ}
    (hc : IsWeight c) (hC : IsWeight C) (hI : IsIdealWeight c C) :
    (unipLat h.2.1 hC).relIndex (unipLat h.2.1 hc) = q ^ ∑ p ∈ upPairs n, (C p.1 p.2 - c p.1 p.2).toNat := by
  rw [Cayley.relIndex_unipLat L ϖ σ q n h c C hc hC hI]
  have h1 := relIndex_upLat_eq_sq L ϖ σ q n h c C hc.1 hC.1 hI.1
  rw [UpLatIndex.relIndex_upLat L ϖ σ q n h c C hI.1, Finset.prod_pow_eq_pow_sum, ← pow_mul, mul_comm, pow_mul] at h1
  exact (Nat.pow_left_injective two_ne_zero h1).symm

theorem v_eq_exp {x : L} (hx : x ≠ 0) : Valued.v x = WithZero.exp (-ordL x) := by
  rw [ordL_eq, neg_neg, WithZero.exp_log (by simpa using hx)]

theorem ord_rev {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (t : torusU σ n) (i : Fin n) :
    ordL (t.1 i.rev : L) = -ordL (t.1 i : L) := by
  have h := (mem_GU_iff σ n _).1 t.2 i i
  rw [← map_inv, diagHom_val, diagHom_val, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h
  have := congrArg Valued.v h
  rw [hσ] at this
  simp [ordL_eq, ← this]

theorem isWeight_ord {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (t : torusU σ n) :
    IsWeight fun i j : Fin n => ordL (t.1 i : L) - ordL (t.1 j : L) :=
  ⟨fun i j => by simp only [ord_rev hσ]; ring, fun i j k _ _ => by simp⟩

theorem conj_entry (t : Fin n → Lˣ) (u : GL (Fin n) L) (i j : Fin n) :
    ((diagHom L (Fin n) t * u * (diagHom L (Fin n) t)⁻¹).val - 1) i j = t i * (u.val - 1) i j * (t j : L)⁻¹ := by
  rw [← map_inv, Units.val_mul, Units.val_mul, diagHom_val, diagHom_val]
  by_cases h : i = j
  · subst h
    simp [mul_sub, sub_mul]
  · simp [Matrix.one_apply, h]

theorem conj_mem_iff {σ : L →+* L} [LocallyCompactSpace (GU σ n)] (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (t : torusU σ n) (u : (borelU σ n).U) :
    conjAut (borelU σ n).U ⟨(borelU σ n).s t, (borelU σ n).Q_le_normalizer ((borelU σ n).s_mem _)⟩ u ∈
      unipLat hσ (isWeight_ord hσ t) ↔ u ∈ unipLat hσ isWeight_zero := by
  rw [mem_unipLat, mem_unipLat, mem_upLat, mem_upLat]
  have e : ∀ i j, ((conjAut (borelU σ n).U
      ⟨(borelU σ n).s t, (borelU σ n).Q_le_normalizer ((borelU σ n).s_mem _)⟩ u).1.1.val - 1) i j =
      t.1 i * (u.1.1.val - 1) i j * (t.1 j : L)⁻¹ := conj_entry t.1 u.1.1
  simp only [e]
  refine and_congr (forall₃_congr fun i j _ => by simp) (forall₃_congr fun i j _ => ?_)
  rw [map_mul, map_mul, map_inv₀, v_eq_exp (t.1 i).ne_zero, v_eq_exp (t.1 j).ne_zero, mul_right_comm,
    ← WithZero.exp_neg, ← WithZero.exp_add, neg_zero, WithZero.exp_zero, neg_sub', sub_eq_add_neg]
  exact mul_le_iff_le_one_right WithZero.exp_pos

theorem exists_idealWeight {c : Fin n → Fin n → ℤ} :
    ∃ C : Fin n → Fin n → ℤ, IsWeight C ∧ IsIdealWeight c C ∧ IsIdealWeight (fun _ _ => 0) C := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i j, |c i j| ≤ M := by
    obtain ⟨M, hM⟩ := (Set.finite_range fun p : Fin n × Fin n => (c p.1 p.2).natAbs).bddAbove
    exact ⟨M, fun i j => by
      have : (c i j).natAbs ≤ M := hM ⟨(i, j), rfl⟩
      rw [← Int.natCast_natAbs]; exact_mod_cast this⟩
  have key : ∀ d : Fin n → Fin n → ℤ, (∀ i j, |d i j| ≤ M) →
      IsIdealWeight d fun i j => (M : ℤ) * (n + i.val - j.val) := by
    intro d hd
    have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    refine ⟨fun i j _ => ?_, fun i j k h1 _ => ?_, fun i j k _ h2 => ?_⟩
    · have h1 : (1 : ℤ) ≤ n + i.val - j.val := by have := j.2; omega
      nlinarith [abs_le.1 (hd i j)]
    · have h1 : (1 : ℤ) ≤ j.val - i.val := by have := Fin.lt_def.1 h1; omega
      nlinarith [abs_le.1 (hd i j)]
    · have h1 : (1 : ℤ) ≤ k.val - j.val := by have := Fin.lt_def.1 h2; omega
      nlinarith [abs_le.1 (hd j k)]
  refine ⟨_, ⟨fun i j => ?_, fun i j k _ _ => ?_⟩, key c hM, key _ fun _ _ => by simp⟩
  · have := i.2
    have := j.2
    simp only [Fin.val_rev]
    congr 1
    omega
  · have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    have h1 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    nlinarith

theorem sum_upPairs (a : Fin n → ℤ) :
    ∑ p ∈ upPairs n, (a p.1 - a p.2) = ∑ i, a i * ((n : ℤ) - 1 - 2 * i.val) := by
  have h1 : ∑ p ∈ upPairs n, a p.1 = ∑ i, a i * ((n : ℤ) - 1 - i.val) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul, mul_comm]
    congr 1
    have := i.2
    omega
  have h2 : ∑ p ∈ upPairs n, a p.2 = ∑ i, a i * (i.val : ℤ) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul, mul_comm]
  rw [Finset.sum_sub_distrib, h1, h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_half (a : Fin n → ℤ) (ha : ∀ i, a i.rev = -a i) :
    ∑ i, a i * ((n : ℤ) - 1 - 2 * i.val) =
      2 * ∑ i : Fin (n / 2), a (Fin.castLE (Nat.div_le_self n 2) i) * ((n : ℤ) - 1 - 2 * i.val) := by
  have h1 : ∑ i : Fin (n / 2), a (Fin.castLE (Nat.div_le_self n 2) i) * ((n : ℤ) - 1 - 2 * i.val) =
      ∑ i : Fin n, if i.val < n / 2 then a i * ((n : ℤ) - 1 - 2 * i.val) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun i _ => Fin.castLE (Nat.div_le_self n 2) i) (fun i _ => by simp)
      (fun i _ j _ e => Fin.castLE_injective _ e) (fun j hj => ⟨⟨j.val, by simpa using hj⟩, by simp, rfl⟩)
      fun i _ => rfl
  rw [two_mul]
  nth_rewrite 2 [h1]
  rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin n => if i.val < n / 2 then a i * ((n : ℤ) - 1 - 2 * i.val) else 0),
    h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.2
  have hr : ((i.rev.val : ℕ) : ℤ) = n - 1 - i.val := by rw [Fin.val_rev]; omega
  simp only [Fin.revPerm_apply, ha, hr]
  split_ifs with h1 h2 h2
  · omega
  · ring
  · ring
  · have : (n : ℤ) - 1 - 2 * i.val = 0 := by omega
    simp [this]

theorem zpow_finset_sum {ι : Type} {z : ℂ} (hz : z ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    z ^ ∑ i ∈ s, a i = ∏ i ∈ s, z ^ a i := by
  first
  | exact @_root_.GlobalTheory.AbelianSumIdentityFirst.main
  | exact _root_.GlobalTheory.AbelianSumIdentityFirst.main
  | (apply _root_.GlobalTheory.AbelianSumIdentityFirst.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbelianSumIdentityFirst.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbelianSumIdentityFirst.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbelianSumIdentityFirst.main ..)

end GlobalTheory.BorelUMod

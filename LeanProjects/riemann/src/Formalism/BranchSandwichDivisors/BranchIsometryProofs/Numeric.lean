import Formalism.BranchSandwichDivisors.NormLog
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Interlace

open Finset

namespace Formalism.BranchingDeterminantCap

private theorem two_pow_le_succ_factorial (j : ℕ) : 2 ^ j ≤ (j + 1).factorial := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, pow_succ]
    calc 2 ^ k * 2 ≤ (k + 1).factorial * (k + 1 + 1) := Nat.mul_le_mul ih (by omega)
      _ = (k + 1 + 1) * (k + 1).factorial := Nat.mul_comm _ _

theorem choose_succ_mul_two_pow_le (r j : ℕ) : r.choose (j + 1) * 2 ^ j ≤ r ^ (j + 1) := by
  calc r.choose (j + 1) * 2 ^ j ≤ r.choose (j + 1) * (j + 1).factorial :=
        Nat.mul_le_mul le_rfl (two_pow_le_succ_factorial j)
    _ = r.descFactorial (j + 1) := by rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_comm]
    _ ≤ r ^ (j + 1) := Nat.descFactorial_le_pow r (j + 1)

theorem geom_half_le (k : ℕ) : ∑ j ∈ range k, ((1 : ℝ) / 2) ^ j ≤ 2 := by
  exact sum_geometric_two_le k

theorem multiplicity_at_place : MultPlace := by
  unfold MultPlace
  intro q k r Nn hq hk hkr hrq hN0 hNn gam hg0 hgs
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith
  have hqne : (q:ℝ) ≠ 0 := hq0.ne'
  have hrq' : (r:ℝ) ≤ (q:ℝ) := by exact_mod_cast hrq
  have hg : ∀ l, 0 ≤ gam l ∧ gam l ≤ (q:ℝ) ^ l := by
    intro l
    cases l with
    | zero => simp [hg0]
    | succ l =>
      rw [hgs l]
      have h1 : (0:ℝ) ≤ (q:ℝ) ^ l := pow_nonneg hq0.le l
      constructor
      · rw [pow_succ]; nlinarith
      · linarith
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', hN0]
  simp only [Nat.cast_one, one_mul, Nat.sub_zero]
  have hterm : ∀ i ∈ range (m + 1), (Nn (i + 1) : ℝ) * gam (m + 1 - (i + 1)) ≤
      (r:ℝ) * (q:ℝ) ^ m * ((1:ℝ) / 2) ^ i := by
    intro i hi
    have him : i ≤ m := by have := Finset.mem_range.mp hi; omega
    have e : m + 1 - (i + 1) = m - i := by omega
    rw [e]
    have hN : (Nn (i + 1) : ℝ) ≤ (r.choose (i + 1) : ℝ) := by exact_mod_cast hNn (i + 1)
    have key : (r.choose (i + 1) : ℝ) * 2 ^ i ≤ (r:ℝ) ^ (i + 1) := by
      exact_mod_cast choose_succ_mul_two_pow_le r i
    have hqs : (q:ℝ) ^ m = (q:ℝ) ^ i * (q:ℝ) ^ (m - i) := by
      rw [← pow_add]; congr 1; omega
    have h2 : ((2:ℝ)) ^ i * ((1:ℝ) / 2) ^ i = 1 := by rw [← mul_pow]; norm_num
    have hpos : (0:ℝ) ≤ ((1:ℝ) / 2) ^ i := by positivity
    have hqm : (0:ℝ) ≤ (q:ℝ) ^ (m - i) := pow_nonneg hq0.le _
    calc (Nn (i + 1) : ℝ) * gam (m - i) ≤ (r.choose (i + 1) : ℝ) * (q:ℝ) ^ (m - i) :=
          mul_le_mul hN (hg _).2 (hg _).1 (Nat.cast_nonneg _)
      _ = (r.choose (i + 1) : ℝ) * 2 ^ i * (q:ℝ) ^ (m - i) * ((1:ℝ) / 2) ^ i := by
          linear_combination (-((r.choose (i + 1) : ℝ) * (q:ℝ) ^ (m - i))) * h2
      _ ≤ (r:ℝ) * (q:ℝ) ^ m * ((1:ℝ) / 2) ^ i := by
          apply mul_le_mul_of_nonneg_right _ hpos
          calc (r.choose (i + 1) : ℝ) * 2 ^ i * (q:ℝ) ^ (m - i)
              ≤ (r:ℝ) ^ (i + 1) * (q:ℝ) ^ (m - i) := mul_le_mul_of_nonneg_right key hqm
            _ = (r:ℝ) * (r:ℝ) ^ i * (q:ℝ) ^ (m - i) := by ring
            _ ≤ (r:ℝ) * (q:ℝ) ^ i * (q:ℝ) ^ (m - i) := by gcongr
            _ = (r:ℝ) * (q:ℝ) ^ m := by rw [hqs]; ring
  have hsum_nonneg : 0 ≤ ∑ i ∈ range (m + 1), (Nn (i + 1) : ℝ) * gam (m + 1 - (i + 1)) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hg _).1)
  have hsum_le : ∑ i ∈ range (m + 1), (Nn (i + 1) : ℝ) * gam (m + 1 - (i + 1)) ≤
      2 * (r:ℝ) * (q:ℝ) ^ m := by
    calc _ ≤ ∑ i ∈ range (m + 1), (r:ℝ) * (q:ℝ) ^ m * ((1:ℝ) / 2) ^ i := Finset.sum_le_sum hterm
      _ = (r:ℝ) * (q:ℝ) ^ m * ∑ i ∈ range (m + 1), ((1:ℝ) / 2) ^ i := by rw [Finset.mul_sum]
      _ ≤ (r:ℝ) * (q:ℝ) ^ m * 2 := by
          apply mul_le_mul_of_nonneg_left (geom_half_le (m + 1)); positivity
      _ = 2 * (r:ℝ) * (q:ℝ) ^ m := by ring
  have hgm : gam (m + 1) = (q:ℝ) ^ (m + 1) - (q:ℝ) ^ m := hgs m
  have hA : (q:ℝ) ^ (m + 1) * (1 - 1 / (q:ℝ)) = (q:ℝ) ^ (m + 1) - (q:ℝ) ^ m := by
    field_simp; ring
  have hB : (q:ℝ) ^ (m + 1) * (1 + (2 * (r:ℝ) - 1) / (q:ℝ)) =
      (q:ℝ) ^ (m + 1) + (2 * (r:ℝ) - 1) * (q:ℝ) ^ m := by
    field_simp; ring
  rw [hA, hB, hgm]
  constructor <;> linarith [hsum_nonneg, hsum_le]

theorem one_sub_sum_le_prod {ι : Type} (s : Finset ι) (x : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ x i)
    (h1 : ∀ i ∈ s, x i ≤ 1) : 1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0' : ∀ i ∈ s, 0 ≤ x i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1' : ∀ i ∈ s, x i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have ih' := ih h0' h1'
    have hxa0 : 0 ≤ x a := h0 a (Finset.mem_insert_self a s)
    have hxa1 : x a ≤ 1 := h1 a (Finset.mem_insert_self a s)
    have hS : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg h0'
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 hxa1), mul_nonneg hxa0 hS]

theorem multiplicity_product : MultProd := by
  unfold MultProd
  intro Pv _ q nn k f r g hcard hr hg hgq hfrg hb
  classical
  have hf : 0 ≤ f := by
    have := Nat.cast_nonneg (α := ℝ) (Fintype.card Pv); linarith
  have hqpos : ∀ v, 0 < q v := fun v => lt_of_lt_of_le hg (hgq v)
  have hq1 : ∀ v, 1 ≤ q v := by
    intro v
    have hc : (1:ℝ) ≤ (Fintype.card Pv : ℝ) := Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr ⟨v⟩)
    have hf2 : (1:ℝ) / 2 ≤ f := by linarith
    have := mul_le_mul hf2 hr (by norm_num) hf
    linarith [hgq v]
  have hgne : g ≠ 0 := hg.ne'
  have hP0 : 0 ≤ ∏ v, q v ^ k := Finset.prod_nonneg (fun v _ => pow_nonneg (hqpos v).le k)
  have hinv0 : ∀ v, 0 ≤ 1 / q v := fun v => le_of_lt (one_div_pos.mpr (hqpos v))
  have hinv1 : ∀ v, 1 / q v ≤ 1 := fun v => by
    have := one_div_le_one_div_of_le one_pos (hq1 v)
    rwa [div_one] at this
  have hsum_inv : ∑ v, 1 / q v ≤ 2 * f / g := by
    calc ∑ v, 1 / q v ≤ ∑ _v : Pv, 1 / g :=
          Finset.sum_le_sum (fun v _ => one_div_le_one_div_of_le hg (hgq v))
      _ = 2 * f / g := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
  constructor
  · have hprod1 : 1 - ∑ v, 1 / q v ≤ ∏ v, (1 - 1 / q v) :=
      one_sub_sum_le_prod Finset.univ (fun v => 1 / q v) (fun v _ => hinv0 v) (fun v _ => hinv1 v)
    have hlow : ∏ v, (q v ^ k * (1 - 1 / q v)) ≤ ∏ v, nn v :=
      Finset.prod_le_prod (fun v _ => mul_nonneg (pow_nonneg (hqpos v).le k) (sub_nonneg.2 (hinv1 v)))
        (fun v _ => (hb v).1)
    rw [Finset.prod_mul_distrib] at hlow
    have h8 : 8 * f * r / g - 2 * f / g = (8 * f * r - 2 * f) / g := by rw [sub_div]
    have h8' : 0 ≤ (8 * f * r - 2 * f) / g := div_nonneg (by nlinarith) hg.le
    have hcoef : 1 - 8 * f * r / g ≤ ∏ v, (1 - 1 / q v) := by linarith
    calc (1 - 8 * f * r / g) * ∏ v, q v ^ k ≤ (∏ v, (1 - 1 / q v)) * ∏ v, q v ^ k :=
          mul_le_mul_of_nonneg_right hcoef hP0
      _ = (∏ v, q v ^ k) * ∏ v, (1 - 1 / q v) := by ring
      _ ≤ ∏ v, nn v := hlow
  · have ha0 : ∀ v, 0 ≤ (2 * r - 1) / q v := fun v => div_nonneg (by linarith) (hqpos v).le
    have hup : ∏ v, nn v ≤ ∏ v, (q v ^ k * (1 + (2 * r - 1) / q v)) :=
      Finset.prod_le_prod
        (fun v _ => le_trans (mul_nonneg (pow_nonneg (hqpos v).le k) (sub_nonneg.2 (hinv1 v))) (hb v).1)
        (fun v _ => (hb v).2)
    rw [Finset.prod_mul_distrib] at hup
    have hexp1 : ∏ v, (1 + (2 * r - 1) / q v) ≤ Real.exp (∑ v, (2 * r - 1) / q v) := by
      rw [Real.exp_sum]
      exact Finset.prod_le_prod (fun v _ => by linarith [ha0 v])
        (fun v _ => by linarith [Real.add_one_le_exp ((2 * r - 1) / q v)])
    have hsum_a : ∑ v, (2 * r - 1) / q v ≤ 4 * f * r / g := by
      have e : ∑ v, (2 * r - 1) / q v = (2 * r - 1) * ∑ v, 1 / q v := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun v _ => by ring)
      rw [e]
      have h2r : 0 ≤ 2 * r - 1 := by linarith
      have e2 : 4 * f * r / g - (2 * r - 1) * (2 * f / g) = 2 * f / g := by ring
      have e3 : 0 ≤ 2 * f / g := div_nonneg (by linarith) hg.le
      nlinarith [mul_le_mul_of_nonneg_left hsum_inv h2r]
    have hfr : 0 ≤ 4 * f * r := by
      have := mul_nonneg hf (by linarith : (0:ℝ) ≤ r); linarith
    have hT0 : 0 ≤ 4 * f * r / g := div_nonneg hfr hg.le
    have hT1 : 4 * f * r / g ≤ 1 := by
      have e4 : (g - 4 * f * r) / g = 1 - 4 * f * r / g := by rw [sub_div, div_self hgne]
      have e5 : 0 ≤ (g - 4 * f * r) / g := div_nonneg (by linarith) hg.le
      linarith
    have hexp2 : Real.exp (4 * f * r / g) ≤ 1 + 2 * (4 * f * r / g) := by
      have hc := convexOn_exp.2 (Set.mem_univ (1:ℝ)) (Set.mem_univ (0:ℝ)) hT0 (sub_nonneg.2 hT1)
        (by ring)
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero, Real.exp_zero] at hc
      have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      nlinarith
    have hprod : ∏ v, (1 + (2 * r - 1) / q v) ≤ 1 + 8 * f * r / g := by
      calc _ ≤ Real.exp (∑ v, (2 * r - 1) / q v) := hexp1
        _ ≤ Real.exp (4 * f * r / g) := Real.exp_le_exp.mpr hsum_a
        _ ≤ 1 + 2 * (4 * f * r / g) := hexp2
        _ = 1 + 8 * f * r / g := by ring
    calc ∏ v, nn v ≤ (∏ v, q v ^ k) * ∏ v, (1 + (2 * r - 1) / q v) := hup
      _ ≤ (∏ v, q v ^ k) * (1 + 8 * f * r / g) := mul_le_mul_of_nonneg_left hprod hP0
      _ = (1 + 8 * f * r / g) * ∏ v, q v ^ k := by ring

theorem interlace_antitone {n : ℕ} {lam : Fin (n + 1) → ℤ} {sg : Fin n → ℤ}
    (h : Interlace lam sg) : Antitone lam := Fin.antitone_iff_succ_le.2 (fun i => (h i).2.trans (h i).1)

theorem cap_factor {n : ℕ} {lam : Fin (n + 1) → ℤ} {sg : Fin n → ℤ} (h : Interlace lam sg)
    (i j : Fin n) (v : ℤ) (hv : v ∈ (rset lam sg i).erase (sg i)) :
    ((v - (i : ℤ)) - (sg j - (j : ℤ))) ≠ 0 ∧
    |((v - (i : ℤ)) - (sg j - (j : ℤ)))| ≤ lam 0 - lam (Fin.last n) + (n : ℤ) - 1 := by
  have hA := interlace_antitone h
  have hv' := Finset.mem_of_mem_erase hv
  have hne : v ≠ sg i := Finset.ne_of_mem_erase hv
  unfold rset at hv'
  rw [Finset.mem_Icc] at hv'
  obtain ⟨hv1, hv2⟩ := hv'
  have hv3 : v ≤ lam i.castSucc := le_trans hv2 (min_le_left _ _)
  have hlo : lam (Fin.last n) ≤ v := le_trans (hA (Fin.le_last _)) hv1
  have hhi : v ≤ lam 0 := le_trans hv3 (hA (Fin.zero_le _))
  have hs1 : lam (Fin.last n) ≤ sg j := le_trans (hA (Fin.le_last _)) (h j).2
  have hs2 : sg j ≤ lam 0 := le_trans (h j).1 (hA (Fin.zero_le _))
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  constructor
  · intro heq
    rcases lt_trichotomy (j : ℕ) (i : ℕ) with hji | hji | hji
    · have h3 : lam i.castSucc ≤ lam j.succ :=
        hA (Fin.le_def.2 (by simp only [Fin.val_succ, Fin.coe_castSucc]; omega))
      have h4 := (h j).2
      omega
    · have hij : j = i := Fin.ext hji
      subst hij
      exact hne (by omega)
    · have h3 : lam j.castSucc ≤ lam i.succ :=
        hA (Fin.le_def.2 (by simp only [Fin.val_succ, Fin.coe_castSucc]; omega))
      have h4 := (h j).1
      omega
  · rw [abs_le]
    constructor <;> omega

private theorem d1_nonneg_of_interlace {n : ℕ} {lam : Fin (n + 1) → ℤ} {sg : Fin n → ℤ}
    (h : Interlace lam sg) : 0 ≤ d1 lam sg := by
  have hd0 : 0 ≤ d0 lam sg := by
    unfold d0; exact Finset.sum_nonneg (fun i _ => sub_nonneg.2 (h i).2)
  unfold d1
  exact Finset.sum_nonneg (fun i _ => le_min (by linarith [(h i).1, (h i).2]) hd0)

theorem capacity_constant_bound : CapConst := by
  unfold CapConst
  intro n lam sg h
  have hd0 : ∀ i : Fin n, sg i - lam i.succ ≤ d0 lam sg := by
    intro i; unfold d0
    exact Finset.single_le_sum (f := fun k : Fin n => sg k - lam k.succ)
      (fun k _ => sub_nonneg.2 (h k).2) (Finset.mem_univ i)
  have hd0nn : 0 ≤ d0 lam sg := by
    unfold d0; exact Finset.sum_nonneg (fun i _ => sub_nonneg.2 (h i).2)
  have hmem : ∀ i : Fin n, sg i ∈ rset lam sg i := by
    intro i; unfold rset; rw [Finset.mem_Icc]
    exact ⟨(h i).2, le_min (h i).1 (by linarith [hd0 i])⟩
  have hcard : ∀ i : Fin n, ((rset lam sg i).erase (sg i)).card =
      (min (lam i.castSucc - lam i.succ) (d0 lam sg)).toNat := by
    intro i
    rw [Finset.card_erase_of_mem (hmem i)]
    unfold rset
    rw [Int.card_Icc]
    have h1 := (h i).1
    have h2 := (h i).2
    have h3 := hd0 i
    omega
  have hm : ∀ i : Fin n, 0 ≤ min (lam i.castSucc - lam i.succ) (d0 lam sg) :=
    fun i => le_min (by linarith [(h i).1, (h i).2]) hd0nn
  have hd1nn : 0 ≤ d1 lam sg := d1_nonneg_of_interlace h
  have hsum : ∑ i : Fin n, ((rset lam sg i).erase (sg i)).card = (d1 lam sg).toNat := by
    rw [Finset.sum_congr rfl (fun i _ => hcard i)]
    have key : ((∑ i : Fin n, (min (lam i.castSucc - lam i.succ) (d0 lam sg)).toNat : ℕ) : ℤ) =
        (((d1 lam sg).toNat : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Int.toNat_of_nonneg hd1nn,
        Finset.sum_congr rfl (fun i _ => Int.toNat_of_nonneg (hm i))]
      unfold d1
      rfl
    exact Nat.cast_injective key
  constructor
  · unfold cCap capEig
    rw [Finset.prod_ne_zero_iff]; intro i _
    rw [Finset.prod_ne_zero_iff]; intro v hv
    rw [Finset.prod_ne_zero_iff]; intro j _
    exact (cap_factor h i j v hv).1
  · unfold cCap capEig
    simp only [Finset.abs_prod]
    calc ∏ i : Fin n, ∏ v ∈ (rset lam sg i).erase (sg i), ∏ j : Fin n,
            |((v - (i : ℤ)) - (sg j - (j : ℤ)))|
        ≤ ∏ i : Fin n, ∏ v ∈ (rset lam sg i).erase (sg i), ∏ _j : Fin n,
            (lam 0 - lam (Fin.last n) + (n : ℤ) - 1) := by
          apply Finset.prod_le_prod
            (fun i _ => Finset.prod_nonneg (fun v _ => Finset.prod_nonneg (fun j _ => abs_nonneg _)))
          intro i _
          apply Finset.prod_le_prod (fun v _ => Finset.prod_nonneg (fun j _ => abs_nonneg _))
          intro v hv
          apply Finset.prod_le_prod (fun j _ => abs_nonneg _)
          intro j _
          exact (cap_factor h i j v hv).2
      _ = (lam 0 - lam (Fin.last n) + (n : ℤ) - 1) ^ (n * (d1 lam sg).toNat) := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, hsum]

theorem capacity_log_bound : CapLog := by
  unfold CapLog
  intro n lam sg a h ha
  obtain ⟨hne, hle⟩ := capacity_constant_bound n lam sg h
  have hd1 := d1_nonneg_of_interlace h
  have hM : (0:ℝ) ≤ ((lam 0 - lam (Fin.last n) : ℤ) : ℝ) := by
    have := interlace_antitone h (Fin.zero_le (Fin.last n))
    exact_mod_cast (by omega : (0:ℤ) ≤ lam 0 - lam (Fin.last n))
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hcpos : (0:ℝ) < |(cCap lam sg : ℝ)| := by
    rw [abs_pos]; exact_mod_cast hne
  have h1 : |(cCap lam sg : ℝ)| ≤
      (((lam 0 - lam (Fin.last n) + (n:ℤ) - 1) : ℤ) : ℝ) ^ (n * (d1 lam sg).toNat) := by
    exact_mod_cast hle
  have e : (((lam 0 - lam (Fin.last n) + (n:ℤ) - 1) : ℤ) : ℝ) =
      ((lam 0 - lam (Fin.last n) : ℤ) : ℝ) + n - 1 := by push_cast; ring
  have hB : |(((lam 0 - lam (Fin.last n) + (n:ℤ) - 1) : ℤ) : ℝ)| ≤ 2 * a := by
    rw [e, abs_le]; constructor <;> linarith
  have h2 : |(cCap lam sg : ℝ)| ≤ (2 * a) ^ (n * (d1 lam sg).toNat) := by
    calc _ ≤ _ := h1
      _ ≤ |(((lam 0 - lam (Fin.last n) + (n:ℤ) - 1) : ℤ) : ℝ)| ^ (n * (d1 lam sg).toNat) := by
          rw [← abs_pow]; exact le_abs_self _
      _ ≤ (2 * a) ^ (n * (d1 lam sg).toNat) := by gcongr
  have ht : (((d1 lam sg).toNat : ℕ) : ℝ) = ((d1 lam sg : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hd1
  calc Real.log |(cCap lam sg : ℝ)| ≤ Real.log ((2 * a) ^ (n * (d1 lam sg).toNat)) :=
        Real.log_le_log hcpos h2
    _ = ((n * (d1 lam sg).toNat : ℕ) : ℝ) * Real.log (2 * a) := Real.log_pow _ _
    _ = ((n:ℝ) + 1 - 1) * ((d1 lam sg : ℤ) : ℝ) * Real.log (2 * a) := by
        rw [Nat.cast_mul, ht]; ring

theorem card_pairs_lt (n : ℕ) :
    ((Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2)).card =
      (n + 1) * n / 2 := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  dsimp only
  have h : ∀ a : Fin (n + 1), (∑ b : Fin (n + 1), if a < b then 1 else 0) = n - (a : ℕ) := by
    intro a
    rw [← Finset.card_filter, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    omega
  rw [Finset.sum_congr rfl (fun a _ => h a)]
  rw [Fin.sum_univ_eq_sum_range (fun k => n - k) (n + 1)]
  have hr := Finset.sum_range_reflect (fun k => k) (n + 1)
  simp only [Nat.add_sub_cancel] at hr
  rw [hr, Finset.sum_range_id, Nat.add_sub_cancel]

theorem weyl_factor {n : ℕ} {nu : Fin (n + 1) → ℤ} (h : Antitone nu) (p : Fin (n + 1) × Fin (n + 1))
    (hp : p.1 < p.2) :
    1 ≤ (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ∧
    (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ≤ ((nu 0 - nu (Fin.last n) : ℤ) : ℝ) + (n : ℝ) := by
  obtain ⟨a, b⟩ := p
  dsimp only at hp ⊢
  have hab : (a : ℕ) < (b : ℕ) := hp
  have hD : nu b ≤ nu a := h hp.le
  have h0 : nu a ≤ nu 0 := h (Fin.zero_le a)
  have hl : nu (Fin.last n) ≤ nu b := h (Fin.le_last b)
  have hn : (1:ℝ) ≤ n := by
    have := b.isLt
    exact_mod_cast (by omega : 1 ≤ n)
  have hd1 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have hDr : (0:ℝ) ≤ ((nu a - nu b : ℤ) : ℝ) := by
    exact_mod_cast (by omega : (0:ℤ) ≤ nu a - nu b)
  have hM : ((nu a - nu b : ℤ) : ℝ) ≤ ((nu 0 - nu (Fin.last n) : ℤ) : ℝ) := by
    exact_mod_cast (by omega : nu a - nu b ≤ nu 0 - nu (Fin.last n))
  have hdpos : (0:ℝ) < ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by linarith
  constructor
  · rw [le_div_iff₀ hdpos]; linarith
  · rw [div_le_iff₀ hdpos]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))
      (le_trans hDr hM), mul_le_mul_of_nonneg_right hn hdpos.le]

theorem weyl_dimension_bound : WeylDimBound := by
  unfold WeylDimBound
  intro n nu h
  constructor
  · calc (1:ℝ) = ∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter
          (fun p => p.1 < p.2), (1:ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun p hp => (weyl_factor h p (Finset.mem_filter.mp hp).2).1)
  · calc _ ≤ ∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter
          (fun p => p.1 < p.2), (((nu 0 - nu (Fin.last n) : ℤ) : ℝ) + (n : ℝ)) :=
          Finset.prod_le_prod
            (fun p hp => le_trans zero_le_one (weyl_factor h p (Finset.mem_filter.mp hp).2).1)
            (fun p hp => (weyl_factor h p (Finset.mem_filter.mp hp).2).2)
      _ = _ := by rw [Finset.prod_const, card_pairs_lt]

theorem weyl_log_bound : WeylLog := by
  unfold WeylLog
  intro n nu a h ha
  obtain ⟨h1, h2⟩ := weyl_dimension_bound n nu h
  have hM : (0:ℝ) ≤ ((nu 0 - nu (Fin.last n) : ℤ) : ℝ) := by
    have := h (Fin.zero_le (Fin.last n))
    exact_mod_cast (by omega : (0:ℤ) ≤ nu 0 - nu (Fin.last n))
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hK : (((n + 1) * n / 2 : ℕ) : ℝ) = ((n:ℝ) + 1) * ((n:ℝ) + 1 - 1) / 2 := by
    have hdvd : 2 ∣ (n + 1) * n := by
      rw [mul_comm]; exact even_iff_two_dvd.mp (Nat.even_mul_succ_self n)
    rw [Nat.cast_div hdvd (by norm_num)]; push_cast; ring
  calc Real.log _ ≤ Real.log ((2 * a) ^ ((n + 1) * n / 2)) := by
        apply Real.log_le_log (by linarith)
        calc _ ≤ _ := h2
          _ ≤ (2 * a) ^ ((n + 1) * n / 2) := by gcongr <;> linarith
    _ = _ := by rw [Real.log_pow, hK]

end Formalism.BranchingDeterminantCap

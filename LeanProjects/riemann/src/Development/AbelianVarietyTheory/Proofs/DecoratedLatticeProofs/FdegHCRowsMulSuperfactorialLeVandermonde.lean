import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
open Formalism.BasicNotions

namespace GlobalTheory.FdegRowsBound

open Finset

theorem pairs_append {p q : ℕ} (g : Fin (p + q) → Fin (p + q) → ℝ) :
    ∏ a : Fin (p + q), ∏ b ∈ univ.filter (fun b => a < b), g a b =
      (∏ i : Fin p, ∏ j ∈ univ.filter (fun j => i < j), g (Fin.castAdd q i) (Fin.castAdd q j)) *
      (∏ i : Fin p, ∏ j : Fin q, g (Fin.castAdd q i) (Fin.natAdd p j)) *
      (∏ i : Fin q, ∏ j ∈ univ.filter (fun j => i < j), g (Fin.natAdd p i) (Fin.natAdd p j)) := by
  simp only [Finset.prod_filter, Fin.prod_univ_add, Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd]
  have h1 : ∀ (i : Fin p) (j : Fin q), (i : ℕ) < p + (j : ℕ) := fun i j => by omega
  have h2 : ∀ (i : Fin q) (j : Fin p), ¬ p + (i : ℕ) < (j : ℕ) := fun i j => by omega
  have h3 : ∀ (i j : Fin q), (p + (i : ℕ) < p + (j : ℕ)) ↔ ((i : ℕ) < (j : ℕ)) := fun i j => by omega
  simp only [h1, h2, h3, if_true, if_false, Finset.prod_const_one, mul_one, one_mul, Finset.prod_mul_distrib]

theorem pairs_cast {n n' : ℕ} (h : n = n') (f : Fin n' → Fin n' → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b => a < b), f (Fin.cast h a) (Fin.cast h b) =
      ∏ a : Fin n', ∏ b ∈ univ.filter (fun b => a < b), f a b := by
  subst h; rfl

theorem den_eq (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      Formalism.MainNotions.StandardLattice.facProd n := by
  unfold Formalism.MainNotions.StandardLattice.facProd
  rcases n with _ | m
  · simp
  have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
  rw [Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial, Nat.cast_prod] at h
  simp only [Finset.filter_lt_eq_Ioi]
  rw [← h]

theorem facProd_pos (n : ℕ) : 0 < Formalism.MainNotions.StandardLattice.facProd n := by
  unfold Formalism.MainNotions.StandardLattice.facProd
  exact Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i

theorem anti_of {K n : ℕ} (hn : K + 1 = n) (u : Fin n → ℚ) (v : Fin K → ℚ)
    (h1 : ∀ i : Fin K, v i < u ⟨i.1, by omega⟩) (h2 : ∀ i : Fin K, u ⟨i.1 + 1, by omega⟩ < v i) :
    StrictAnti u := by
  subst hn
  exact Fin.strictAnti_iff_succ_lt.2 fun i => (h2 i).trans (h1 i)

theorem mono_of {m : ℕ} (f : Fin m → ℚ) (h : ∀ j : Fin m, ∀ hj : j.1 + 1 < m, f j < f ⟨j.1 + 1, hj⟩) :
    StrictMono f := by
  rcases m with _ | m
  · exact fun a => a.elim0
  · exact Fin.strictMono_iff_lt_succ.2 fun i => h (Fin.castSucc i) (by simp)

theorem vand_cast {K : ℕ} (u : Fin (K + 1) → ℝ) :
    Formalism.MainNotions.StandardLattice.vand u = ∏ i : Fin K, ∏ j : Fin K,
      (if i ≤ j then u (Fin.castSucc i) - u (Fin.succ j) else 1) := by
  unfold Formalism.MainNotions.StandardLattice.vand
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ b ∈ univ.filter (fun b => Fin.last K < b), (u (Fin.last K) - u b) = 1 := by
    apply Finset.prod_eq_one
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact absurd hb (not_lt.2 (Fin.le_last b))
  rw [hlast, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_filter, Fin.prod_univ_succ]
  simp [Fin.castSucc_lt_succ_iff]

theorem interlace_bound {K n : ℕ} (hn : K + 1 = n) (u : Fin n → ℝ) (v : Fin K → ℝ)
    (h1 : ∀ i : Fin K, v i < u ⟨i.1, by omega⟩) (h2 : ∀ i : Fin K, u ⟨i.1 + 1, by omega⟩ < v i)
    (h3 : ∀ i : Fin K, 1 ≤ u ⟨i.1, by omega⟩ - u ⟨i.1 + 1, by omega⟩) :
    ∏ a : Fin K, ∏ b ∈ univ.filter (fun b => a < b), |v a - v b| ≤ Formalism.MainNotions.StandardLattice.vand u := by
  subst hn
  have hu : StrictAnti u := Fin.strictAnti_iff_succ_lt.2 fun i => (h2 i).trans (h1 i)
  rw [vand_cast]
  simp only [Finset.prod_filter]
  apply Finset.prod_le_prod
  · intro i _
    exact Finset.prod_nonneg fun j _ => by split_ifs <;> positivity
  intro i _
  apply Finset.prod_le_prod
  · intro j _; split_ifs <;> positivity
  intro j _
  by_cases hij : i < j
  · have hle : i ≤ j := hij.le
    simp only [hij, hle, if_true]
    have hsj : Fin.succ i ≤ Fin.castSucc j := by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.coe_castSucc]; exact hij
    have a1 := h1 i
    have a2 := h2 j
    have a3 := h1 j
    have a4 := h2 i
    have a5 := hu.antitone hsj
    have e1 : u ⟨i.1, by omega⟩ = u (Fin.castSucc i) := rfl
    have e2 : u ⟨j.1 + 1, by omega⟩ = u (Fin.succ j) := rfl
    have e3 : u ⟨j.1, by omega⟩ = u (Fin.castSucc j) := rfl
    have e4 : u ⟨i.1 + 1, by omega⟩ = u (Fin.succ i) := rfl
    rw [abs_of_pos (by linarith)]
    linarith
  · simp only [hij, if_false]
    by_cases hle : i ≤ j
    · have : i = j := le_antisymm hle (not_lt.1 hij)
      subst this
      simp only [hle, if_true]
      exact h3 i
    · simp [hle]

theorem lamSH_congr (R : Ranks) (P Q : HCParam R) (hv : Q.v = P.v) (hb : Q.b = P.b) :
    Formalism.MainNotions.S.lamSH R P = Formalism.MainNotions.S.lamSH R Q := by
  unfold Formalism.MainNotions.S.lamSH Formalism.MainNotions.S.lamS; rw [hv, hb]

theorem lamS_left (R : Ranks) (P : HCParam R) (h : (R.k - 1) + R.m = R.r) (i : Fin (R.k - 1)) :
    Formalism.MainNotions.S.lamS R P (Fin.cast h (Fin.castAdd R.m i)) = (P.v i : ℝ) := by
  simp [Formalism.MainNotions.S.lamS]

theorem lamS_right (R : Ranks) (P : HCParam R) (h : (R.k - 1) + R.m = R.r) (j : Fin R.m) :
    Formalism.MainNotions.S.lamS R P (Fin.cast h (Fin.natAdd (R.k - 1) j)) = -(P.b j : ℝ) := by
  simp [Formalism.MainNotions.S.lamS]

theorem count_pairs (m : ℕ) :
    ∑ j : Fin m, (univ.filter (fun j' : Fin m => j < j')).card = m * (m - 1) / 2 := by
  simp only [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m, Finset.sum_range_reflect (fun i => i) m]
  exact Finset.sum_range_id m

theorem fdeg_rows_le : ∀ (R : Ranks) (P Q : HCParam R), Q.v = P.v → Q.b = P.b → ∀ B : ℝ, 1 ≤ B →
    (∀ i j, ((P.v i : ℚ) : ℝ) + ((P.b j : ℚ) : ℝ) ≤ B) →
    (∀ j j', ((P.b j' : ℚ) : ℝ) - ((P.b j : ℚ) : ℝ) ≤ B) →
    Formalism.QuantumDeterminants.fdegHC (Formalism.MainNotions.S.lamSH R P) * Formalism.MainNotions.StandardLattice.facProd R.r ≤
      B ^ ((R.k - 1) * R.m + R.m * (R.m - 1) / 2) * Formalism.MainNotions.StandardLattice.vand (fun i => ((Q.u i : ℚ) : ℝ)) := by
  intro R P Q hv hb B hB1 hvb hbb
  rw [lamSH_congr R P Q hv hb]
  rw [← hv, ← hb] at hvb
  rw [← hb] at hbb
  have hk := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have hr : (R.k - 1) + R.m = R.r := by simp only [Ranks.r]; omega
  have huanti : StrictAnti Q.u := anti_of (by omega : R.k - 1 + 1 = R.k) Q.u Q.v Q.u_gt_v Q.v_gt_u
  have hbmono : StrictMono Q.b := mono_of Q.b fun j hj => by
    have a1 := Q.gap_be j
    have a2 := Q.gap_eb j hj
    have : (0:ℚ) ≤ R.t := by positivity
    linarith
  have hpos : ∀ i j, 0 < ((Q.v i : ℚ) : ℝ) + ((Q.b j : ℚ) : ℝ) := by
    intro i j
    have a1 := Q.v_gt_u i
    have a2 : Q.u ⟨R.k - 1, by omega⟩ ≤ Q.u ⟨i.1 + 1, by omega⟩ :=
      huanti.antitone (by rw [Fin.le_def]; simp only; omega)
    have a3 := Q.u_last_gt (by omega) (by omega)
    have a4 : Q.b ⟨0, by omega⟩ ≤ Q.b j := hbmono.monotone (by rw [Fin.le_def]; simp)
    have : (0:ℚ) < Q.v i + Q.b j := by linarith
    exact_mod_cast this
  have h3 : ∀ i : Fin (R.k - 1), (1:ℝ) ≤ ((Q.u ⟨i.1, by omega⟩ : ℚ) : ℝ) - ((Q.u ⟨i.1 + 1, by omega⟩ : ℚ) : ℝ) := by
    intro i
    obtain ⟨z, hz⟩ := Q.u_half ⟨i.1, by omega⟩
    obtain ⟨z', hz'⟩ := Q.u_half ⟨i.1 + 1, by omega⟩
    have a := (Q.v_gt_u i).trans (Q.u_gt_v i)
    rw [hz, hz'] at a
    have b1 : z' < z := by exact_mod_cast (by linarith : (z':ℚ) < z)
    have b2 : (z':ℚ) + 1 ≤ z := by exact_mod_cast b1
    have : (1:ℚ) ≤ Q.u ⟨i.1, by omega⟩ - Q.u ⟨i.1 + 1, by omega⟩ := by rw [hz, hz']; linarith
    exact_mod_cast this
  have hden := den_eq (2 * R.rS + R.k + 1)
  have hfp : Formalism.MainNotions.StandardLattice.facProd (2 * R.rS + R.k + 1) = Formalism.MainNotions.StandardLattice.facProd R.r := by rw [Formalism.MainNotions.S.dimS_eq]
  unfold Formalism.QuantumDeterminants.fdegHC
  rw [hden, hfp, div_mul_cancel₀ _ (facProd_pos _).ne']
  unfold Formalism.MainNotions.S.lamSH
  have e1 := pairs_cast (Formalism.MainNotions.S.dimS_eq R) (fun a b => |Formalism.MainNotions.S.lamS R Q a - Formalism.MainNotions.S.lamS R Q b|)
  have e2 := pairs_cast hr (fun a b => |Formalism.MainNotions.S.lamS R Q a - Formalism.MainNotions.S.lamS R Q b|)
  beta_reduce at e1 e2
  rw [e1, ← e2, pairs_append]
  simp only [lamS_left, lamS_right]
  have hA : ∏ i : Fin (R.k - 1), ∏ j ∈ univ.filter (fun j => i < j),
      |((Q.v i : ℚ) : ℝ) - ((Q.v j : ℚ) : ℝ)| ≤ Formalism.MainNotions.StandardLattice.vand (fun i => ((Q.u i : ℚ) : ℝ)) :=
    interlace_bound (by omega : R.k - 1 + 1 = R.k) (fun i => ((Q.u i : ℚ) : ℝ)) (fun i => ((Q.v i : ℚ) : ℝ))
      (fun i => by exact_mod_cast Q.u_gt_v i) (fun i => by exact_mod_cast Q.v_gt_u i) h3
  have hC : ∏ i : Fin (R.k - 1), ∏ j : Fin R.m, |((Q.v i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| ≤
      B ^ ((R.k - 1) * R.m) := by
    calc _ ≤ ∏ i : Fin (R.k - 1), ∏ j : Fin R.m, B :=
          Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)
            (fun i _ => Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => by
              rw [sub_neg_eq_add, abs_of_pos (hpos i j)]; exact hvb i j))
      _ = B ^ ((R.k - 1) * R.m) := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  have hD : ∏ i : Fin R.m, ∏ j ∈ univ.filter (fun j => i < j),
      |-((Q.b i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| ≤ B ^ (R.m * (R.m - 1) / 2) := by
    calc _ ≤ ∏ i : Fin R.m, ∏ j ∈ univ.filter (fun j => i < j), B :=
          Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)
            (fun i _ => Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j hj => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              have c1 : ((Q.b i : ℚ) : ℝ) < ((Q.b j : ℚ) : ℝ) := by exact_mod_cast hbmono hj
              have c2 := hbb i j
              rw [abs_le]; constructor <;> linarith))
      _ = ∏ i : Fin R.m, B ^ (univ.filter (fun j => i < j)).card := by
          simp only [Finset.prod_const]
      _ = B ^ (∑ i : Fin R.m, (univ.filter (fun j => i < j)).card) := Finset.prod_pow_eq_pow_sum _ _ _
      _ = B ^ (R.m * (R.m - 1) / 2) := by rw [count_pairs]
  have nA : 0 ≤ ∏ i : Fin (R.k - 1), ∏ j ∈ univ.filter (fun j => i < j),
      |((Q.v i : ℚ) : ℝ) - ((Q.v j : ℚ) : ℝ)| :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _
  have nC : 0 ≤ ∏ i : Fin (R.k - 1), ∏ j : Fin R.m, |((Q.v i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _
  have nD : 0 ≤ ∏ i : Fin R.m, ∏ j ∈ univ.filter (fun j => i < j),
      |-((Q.b i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _
  have hB0 : (0:ℝ) ≤ B := by linarith
  calc _ ≤ Formalism.MainNotions.StandardLattice.vand (fun i => ((Q.u i : ℚ) : ℝ)) * B ^ ((R.k - 1) * R.m) * B ^ (R.m * (R.m - 1) / 2) :=
        mul_le_mul (mul_le_mul hA hC nC (nA.trans hA)) hD nD
          (mul_nonneg (nA.trans hA) (pow_nonneg hB0 _))
    _ = _ := by rw [pow_add]; ring

end GlobalTheory.FdegRowsBound

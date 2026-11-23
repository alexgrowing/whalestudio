import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.EvaluationSums.EvhEqSum

noncomputable section

namespace PositivityTheory.KB

open ChainCochainPairing

private theorem val_succAbove_eq_ite_lt {n : ℕ} (q : Fin (n + 1)) (j : Fin n) :
    ((q.succAbove j : Fin (n + 1)) : ℕ) = if (j : ℕ) < q then (j : ℕ) else (j : ℕ) + 1 := by
  by_cases h : (j : ℕ) < q
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    simp [h]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]
    simp [h]

private theorem ev_eq_linearCombination {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (F : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ F y z = Finsupp.linearCombination ℝ (fun g : Fin m → G ↦ F fun j ↦ ρ (Fin.partialProd g j) • y) z := by
  simp [ev, Finsupp.linearCombination_apply, smul_eq_mul]

private theorem ev_bd_eq_ev_dC_of_inv {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (F : (Fin (m + 1) → Y) → ℝ) (hF : Inv ρ F) (y : Y) (w : Chn G (m + 1)) :
    ev ρ F y (bd G m w) = ev ρ (dC F) y w := by
  rw [ev_eq_linearCombination, ev_eq_linearCombination, ← LinearMap.comp_apply]
  congr 1
  ext g
  simp [bd, dC, Fin.sum_univ_succ (n := m + 1), Fin.partialProd_contractNth]
  simp_rw [Fin.partialProd_succ', map_mul, mul_smul]
  exact (hF (g 0) _).symm

private theorem dC_prism_sum_eq_snd_sub_fst {Y : Type} {n : ℕ} (F : (Fin (n + 2) → Y) → ℝ) (hd : dC F = 0)
    (u : Fin (n + 2) → Y × Y) :
    dC (fun v : Fin (n + 1) → Y × Y ↦ ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) *
      F (fun p : Fin (n + 2) ↦ if (p : ℕ) ≤ i then (v ⟨min p n, by omega⟩).1
        else (v ⟨p - 1, by have := p.isLt; omega⟩).2)) u =
      F (fun p ↦ (u p).2) - F (fun p ↦ (u p).1) := by
  classical
  let uu : ℕ → Y × Y := fun j ↦ u ⟨min j (n + 1), by omega⟩
  let s : ℕ → ℕ → ℕ := fun q j ↦ if j < q then j else j + 1
  let FP : ℕ → ℕ → Fin (n + 2) → Y := fun q i p ↦
    if (p : ℕ) ≤ i then (uu (s q (min p n))).1 else (uu (s q (p - 1))).2
  let S : ℕ → ℕ → ℝ := fun q i ↦ (-1) ^ (q + i) * F (FP q i)
  have hL : dC (fun v : Fin (n + 1) → Y × Y ↦ ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) *
      F (fun p : Fin (n + 2) ↦ if (p : ℕ) ≤ i then (v ⟨min p n, by omega⟩).1
        else (v ⟨p - 1, by have := p.isLt; omega⟩).2)) u =
      ∑ q ∈ Finset.range (n + 2), ∑ i ∈ Finset.range (n + 1), S q i := by
    unfold dC
    rw [← Fin.sum_univ_eq_sum_range (fun q ↦ ∑ i ∈ Finset.range (n + 1), S q i)]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ S q i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [S, pow_add, mul_assoc]
    congr 2
    congr 1
    funext p
    simp only [Function.comp, FP, uu, s]
    split_ifs <;> (congr 2; apply Fin.ext; rw [val_succAbove_eq_ite_lt]; simp only [Fin.val_mk]; split_ifs <;> omega)
  let M : ℕ → Fin (n + 2) → Y := fun i r ↦ if (r : ℕ) < i then (uu r).1 else (uu r).2
  have hstep : ∀ i, i < n + 2 → F (M i) - F (M (i + 1)) =
      ∑ p ∈ Finset.range i, S p (i - 1) + ∑ q ∈ Finset.Ico (i + 1) (n + 2), S q i := by
    intro i hi
    let T' : ℕ → Y := fun r ↦ if r ≤ i then (uu r).1 else (uu (r - 1)).2
    let c : ℕ → ℝ := fun p ↦ (-1 : ℝ) ^ p * F (fun r : Fin (n + 2) ↦ T' (s p r))
    have hc : ∑ p ∈ Finset.range (n + 3), c p = 0 := by
      have h0 := congrFun hd (fun r : Fin (n + 3) ↦ T' r)
      simp only [dC, Pi.zero_apply] at h0
      rw [← Fin.sum_univ_eq_sum_range c, ← h0]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      simp only [c]
      congr 2
      funext r
      simp only [s]
      rw [val_succAbove_eq_ite_lt]
    rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ n + 3 by omega),
      Finset.sum_eq_sum_Ico_succ_bot (show i < n + 3 by omega),
      Finset.sum_eq_sum_Ico_succ_bot (show i + 1 < n + 3 by omega)] at hc
    have hA : ∑ p ∈ Finset.range i, S p (i - 1) = -(-1 : ℝ) ^ i * ∑ p ∈ Finset.range i, c p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [Finset.mem_range] at hp
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [S, c, Nat.add_sub_cancel]
      have hf : FP p j = fun r : Fin (n + 2) ↦ T' (s p r) := by
        funext r
        simp only [FP, T', s]
        split_ifs <;> first | omega | (congr 2 <;> omega)
      rw [hf, pow_add, pow_succ]
      ring
    have hB : ∑ q ∈ Finset.Ico (i + 1) (n + 2), S q i =
        -(-1 : ℝ) ^ i * ∑ p ∈ Finset.Ico (i + 1 + 1) (n + 3), c p := by
      have hre : ∑ p ∈ Finset.Ico (i + 1 + 1) (n + 3), c p =
          ∑ q ∈ Finset.Ico (i + 1) (n + 2), c (q + 1) := by
        rw [Finset.sum_Ico_add']
      rw [hre, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q hq ↦ ?_
      rw [Finset.mem_Ico] at hq
      simp only [S, c]
      have hf : FP q i = fun r : Fin (n + 2) ↦ T' (s (q + 1) r) := by
        funext r
        simp only [FP, T', s]
        split_ifs <;> first | omega | (congr 2 <;> omega)
      rw [hf, pow_add, pow_succ]
      ring
    have hci : c i = (-1 : ℝ) ^ i * F (M i) := by
      simp only [c]
      congr 2
      funext r
      simp only [T', s, M]
      split_ifs <;> first | omega | (congr 2 <;> omega)
    have hci1 : c (i + 1) = -((-1 : ℝ) ^ i * F (M (i + 1))) := by
      simp only [c]
      rw [pow_succ]
      have hf : (fun r : Fin (n + 2) ↦ T' (s (i + 1) r)) = M (i + 1) := by
        funext r
        simp only [T', s, M]
        split_ifs <;> first | omega | (congr 2 <;> omega)
      rw [hf]
      ring
    have hε : ((-1 : ℝ) ^ i) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [hci, hci1] at hc
    rw [hA, hB]
    linear_combination (-1 : ℝ) ^ i * hc - (F (M i) - F (M (i + 1))) * hε
  have hM0 : M 0 = fun p ↦ (u p).2 := by
    funext r
    simp only [M, uu, Nat.not_lt_zero, if_false]
    congr 2
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  have hM1 : M (n + 2) = fun p ↦ (u p).1 := by
    funext r
    simp only [M, uu, r.isLt, if_true]
    congr 2
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  rw [hL, ← hM0, ← hM1, ← Finset.sum_range_sub' (fun i ↦ F (M i)),
    Finset.sum_congr rfl (fun i hi ↦ hstep i (Finset.mem_range.mp hi)), Finset.sum_add_distrib,
    Finset.sum_range_succ' (fun i ↦ ∑ p ∈ Finset.range i, S p (i - 1)),
    Finset.sum_range_succ (fun i ↦ ∑ q ∈ Finset.Ico (i + 1) (n + 2), S q i)]
  simp only [Finset.range_zero, Finset.sum_empty, Finset.Ico_self, add_zero, Nat.add_sub_cancel]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j hj ↦ ?_).symm
  rw [Finset.mem_range] at hj
  exact Finset.sum_range_add_sum_Ico _ (by omega)

theorem sEv_of : SEv := by
  intro G H Y _ _ _ ρ k F hF hd
  refine ⟨fun y z hz ↦ ?_, fun y y' z hz ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := hz
    rw [ev_bd_eq_ev_dC_of_inv ρ F hF y w, hd]
    simp [ev]
  · have hΦ : Inv ρ (fun v : Fin (k + 1) → Y × Y ↦ ∑ i : Fin (k + 1), (-1) ^ (i : ℕ) *
        F (fun p : Fin (k + 2) ↦ if (p : ℕ) ≤ i then (v ⟨min p k, by omega⟩).1
          else (v ⟨p - 1, by have := p.isLt; omega⟩).2)) := by
      intro g v
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      congr 1
      refine Eq.trans ?_ (hF g _)
      congr 1
      funext p
      split_ifs <;> rfl
    have h0 := ev_bd_eq_ev_dC_of_inv ρ _ hΦ (y', y) z
    rw [show bd G k z = 0 from hz] at h0
    have e : dC (fun v : Fin (k + 1) → Y × Y ↦ ∑ i : Fin (k + 1), (-1) ^ (i : ℕ) *
        F (fun p : Fin (k + 2) ↦ if (p : ℕ) ≤ i then (v ⟨min p k, by omega⟩).1
          else (v ⟨p - 1, by have := p.isLt; omega⟩).2)) =
        fun u ↦ F (fun p ↦ (u p).2) - F (fun p ↦ (u p).1) := funext (dC_prism_sum_eq_snd_sub_fst F hd)
    rw [e] at h0
    simp only [ev, Finsupp.sum, Prod.smul_fst, Prod.smul_snd, mul_sub, Finset.sum_sub_distrib,
      map_zero, Finsupp.support_zero, Finset.sum_empty] at h0
    simp only [ev, Finsupp.sum]
    linarith

end PositivityTheory.KB

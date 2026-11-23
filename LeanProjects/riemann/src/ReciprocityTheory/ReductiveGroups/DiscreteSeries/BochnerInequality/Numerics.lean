import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NumRho

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Num

variable {ε : Fin n → Bool}

private theorem dot_add_l (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, sum_add_distrib]

private theorem dot_add_r (u v w : Fin n → ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, sum_add_distrib]

private theorem dot_comm' (u v : Fin n → ℝ) : dot u v = dot v u := by
  simp only [dot, mul_comm]

private theorem dot_neg_r (u v : Fin n → ℝ) : dot u (-v) = - dot u v := by
  simp only [dot, Pi.neg_apply, mul_neg, sum_neg_distrib]

private theorem dot_sum_r {k : ℕ} (u : Fin n → ℝ) (f : Fin k → Fin n → ℝ) :
    dot u (∑ i, f i) = ∑ i, dot u (f i) := by
  simp only [dot, Finset.sum_apply, mul_sum]
  exact Finset.sum_comm

private theorem dot_root_r (u : Fin n → ℝ) (a b : Fin n) : dot u (root a b) = u a - u b := by
  simp [dot, root, Pi.single_apply, mul_sub, sum_sub_distrib]

private theorem root_swap (a b : Fin n) : root b a = - root a b := by
  simp [root]

private theorem nsq_nonneg'' (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact sum_nonneg fun i _ => mul_self_nonneg (u i)

private theorem nsq_add'' (u v : Fin n → ℝ) : nsq (u + v) = nsq u + 2 * dot u v + nsq v := by
  simp only [nsq, dot_add_l, dot_add_r, dot_comm' v u]; ring

private theorem dot_le_sqrt (u v : Fin n → ℝ) : dot u v ≤ √(nsq u) * √(nsq v) := by
  rw [← Real.sqrt_mul (nsq_nonneg'' u)]
  refine le_trans (le_abs_self _) ?_
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  simpa [dot, nsq, sq] using Finset.sum_mul_sq_le_sq_mul_sq univ u v

private theorem sqrt_nsq_add_le (u v : Fin n → ℝ) : √(nsq (u + v)) ≤ √(nsq u) + √(nsq v) := by
  have h1 : nsq (u + v) ≤ (√(nsq u) + √(nsq v)) ^ 2 := by
    rw [nsq_add'', add_sq, Real.sq_sqrt (nsq_nonneg'' u), Real.sq_sqrt (nsq_nonneg'' v)]
    nlinarith [dot_le_sqrt u v]
  calc √(nsq (u + v)) ≤ √((√(nsq u) + √(nsq v)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)

private theorem sqrt_nsq_sum_le {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℝ) :
    √(nsq (∑ i ∈ s, f i)) ≤ ∑ i ∈ s, √(nsq (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nsq, dot]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (sqrt_nsq_add_le _ _).trans (by linarith)

private theorem pq_facts {a b : Fin n} (hε : ε a ≠ ε b) :
    1 ≤ (pOf ε : ℝ) ∧ 1 ≤ (qOf ε : ℝ) ∧ (pOf ε : ℝ) + (qOf ε : ℝ) = n := by
  have hsum : pOf ε + qOf ε = n := by
    unfold pOf qOf
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun a => ε a = true)
    simpa using this
  have hp : ∃ c, ε c = true := by
    cases ha : ε a
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
    · exact ⟨a, ha⟩
  have hq : ∃ c, ε c = false := by
    cases ha : ε a
    · exact ⟨a, ha⟩
    · exact ⟨b, by cases hb : ε b <;> simp_all⟩
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  have h1 : 1 ≤ pOf ε := Finset.card_pos.mpr ⟨c, by simp [hc]⟩
  have h2 : 1 ≤ qOf ε := Finset.card_pos.mpr ⟨d, by simp [hd]⟩
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast hsum⟩

theorem gap_gt {a b : Fin n} (hε : ε a ≠ ε b) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) :
    2 * (n : ℝ) - 3 < h ∧ (n : ℝ) - 1 < h := by
  obtain ⟨hp, hq, hn⟩ := pq_facts hε
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm := mul_nonneg (sub_nonneg.2 hp) (sub_nonneg.2 hq)
  have key : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by
    nlinarith [mul_nonneg hn0 hm]
  constructor
  · nlinarith [sq_nonneg ((n : ℝ) - 2)]
  · nlinarith [sq_nonneg ((n : ℝ) - 1)]

theorem sch_gap {lam : Fin n → ℝ} (hgap : StdGap ε lam) {a b : Fin n} (hab : a < b)
    (hε : ε a ≠ ε b) : 1 + 2 * dot (rhoC ε) (rhoN ε) < dot lam (root a b) := by
  obtain ⟨hanti, h, hg, hbig⟩ := hgap
  have h1 := hg a b hε
  have hlt : lam b < lam a := hanti hab
  rw [abs_of_pos (sub_pos.2 hlt)] at h1
  rw [dot_root_r]
  linarith [two_dot_rhoC_rhoN_le ε]

theorem crossVal_pos {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    2 * (h - n + 1) ≤
      casValK ε (lowK ε lam + root a b) - n - casValK ε (lowK ε lam) := by
  rw [casValK_add, lowK_add_rhoC, nsq_root (ne_of_lt hab), dot_add_l, dot_root_r lam]
  have h1 := hh a b hε
  rw [abs_of_pos (sub_pos.2 (hmono hab))] at h1
  have h2 := dot_rhoN_root_ge hab hε
  linarith

theorem crossVal_neg {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    casValK ε (lowK ε lam + root b a) - n - casValK ε (lowK ε lam) ≤ -2 * h - 2 := by
  rw [casValK_add, lowK_add_rhoC, nsq_root (ne_of_gt hab), dot_add_l, dot_root_r lam,
    root_swap a b, dot_neg_r]
  have h1 := hh a b hε
  rw [abs_of_pos (sub_pos.2 (hmono hab))] at h1
  have h2 := dot_rhoN_root_ge hab hε
  linarith

theorem isNCSum_zero {ν : Fin n → ℝ} : IsNCSum ε 0 ν ↔ ν = 0 := by
  constructor
  · rintro ⟨γ, -, rfl⟩
    simp
  · rintro rfl
    exact ⟨Fin.elim0, fun i => i.elim0, by simp⟩

theorem isNCSum_succ_exists {k : ℕ} {ν : Fin n → ℝ} (hν : IsNCSum ε (k + 1) ν) :
    ∃ a b : Fin n, ε a ≠ ε b := by
  obtain ⟨γ, hγ, -⟩ := hν
  exact ⟨_, _, hγ 0⟩

theorem vogan_num {Λ ν : Fin n → ℝ} {j : ℕ} (hj : 1 ≤ j) (hν : IsNCSum ε j ν) {h : ℝ}
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hc : casValK ε Λ + 2 * (j : ℝ) * (h - n + 1) ≤ casValK ε (Λ + ν)) :
    nsq (Λ + (2 : ℝ) • rhoC ε) ≤ nsq (Λ + ν + (2 : ℝ) • rhoC ε) := by
  obtain ⟨γ, hγ, rfl⟩ := hν
  obtain ⟨hg1, hg2⟩ := gap_gt (hγ ⟨0, hj⟩) hbig
  have hρ : -((j : ℝ) * (((n : ℝ) - 2) / 2)) ≤ dot (rhoC ε) (∑ i, root (γ i).1 (γ i).2) := by
    rw [dot_sum_r]
    have : ∑ _i : Fin j, -(((n : ℝ) - 2) / 2) ≤ ∑ i, dot (rhoC ε) (root (γ i).1 (γ i).2) := by
      apply Finset.sum_le_sum
      intro i _
      have := abs_dot_root_rhoC_le (ε := ε) (hγ i)
      rw [dot_comm'] at this
      linarith [neg_abs_le (dot (rhoC ε) (root (γ i).1 (γ i).2))]
    simpa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg] using this
  rw [casValK_add] at hc
  have e2 : Λ + (2 : ℝ) • rhoC ε = (Λ + rhoC ε) + rhoC ε := by rw [two_smul]; abel
  have e3 : Λ + (∑ i, root (γ i).1 (γ i).2) + (2 : ℝ) • rhoC ε =
      ((Λ + rhoC ε) + rhoC ε) + ∑ i, root (γ i).1 (γ i).2 := by rw [two_smul]; abel
  rw [e2, e3, nsq_add'' ((Λ + rhoC ε) + rhoC ε), dot_add_l]
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hpos : 0 ≤ 2 * h - 3 * (n : ℝ) + 4 := by linarith
  nlinarith [mul_nonneg hj0 hpos]

theorem degree_num {Λ ν : Fin n → ℝ} {j k : ℕ} (hjk : j ≤ k) (hν : IsNCSum ε j ν) :
    casValK ε (Λ + ν) ≤ (√(nsq (Λ + rhoC ε)) + √2 * k) ^ 2 - nsq (rhoC ε) := by
  obtain ⟨γ, hγ, rfl⟩ := hν
  have hs : √(nsq (∑ i, root (γ i).1 (γ i).2)) ≤ √2 * k := by
    refine (sqrt_nsq_sum_le _ _).trans ?_
    have : ∀ i, √(nsq (root (γ i).1 (γ i).2)) = √2 := fun i => by
      rw [nsq_root (fun e => hγ i (by rw [e]))]
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hjk) (Real.sqrt_nonneg 2)
  unfold casValK
  have e : Λ + (∑ i, root (γ i).1 (γ i).2) + rhoC ε = (Λ + rhoC ε) + ∑ i, root (γ i).1 (γ i).2 := by
    abel
  rw [e]
  have h1 := (sqrt_nsq_add_le (Λ + rhoC ε) (∑ i, root (γ i).1 (γ i).2)).trans (by linarith [hs] :
    √(nsq (Λ + rhoC ε)) + √(nsq (∑ i, root (γ i).1 (γ i).2)) ≤ √(nsq (Λ + rhoC ε)) + √2 * k)
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rw [Real.sq_sqrt (nsq_nonneg'' _)] at h2
  linarith

end Num

end ReciprocityTheory.ChartRestriction.DS

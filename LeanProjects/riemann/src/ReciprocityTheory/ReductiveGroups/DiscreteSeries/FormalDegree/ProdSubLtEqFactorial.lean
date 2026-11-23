import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdDefs

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem sCoef_lamT (lam : Fin n → ℝ) (t : ℕ) {i : ℕ} (hi : i + 1 < n) :
    sCoef (lamT lam t) i = sCoef lam i + t := by
  simp only [sCoef, dif_pos hi, lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.val_mk]
  push_cast
  ring

theorem sCoef_zero_of (i : ℕ) (hi : i + 1 < n) : sCoef (0 : Fin n → ℝ) i = 1 := by
  simp [sCoef, hi]

theorem ph_lamT (lam : Fin n → ℝ) (t : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Ph (lamT lam t) X = Ph lam X + (t : ℝ) * Ph (0 : Fin n → ℝ) X := by
  unfold Ph
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i + 1 < n := by
    have := Finset.mem_range.mp hi
    omega
  rw [sCoef_lamT lam t hi', sCoef_zero_of i hi']
  ring

theorem dvec_antitone : Antitone (Dvec n) := by
  intro a b hab
  simp only [Dvec]
  have h1 : (a : ℕ) ≤ (b : ℕ) := hab
  have h2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast h1
  linarith

theorem lamT_apply (lam : Fin n → ℝ) (t : ℕ) (a : Fin n) :
    lamT lam t a = lam a + (t : ℝ) * ((n : ℝ) - 1 - ((a : ℕ) : ℝ)) := by
  simp only [lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem lamT_sub (lam : Fin n → ℝ) (t : ℕ) (a b : Fin n) :
    lamT lam t a - lamT lam t b = (lam a - lam b) + (t : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  rw [lamT_apply, lamT_apply]
  ring

theorem strictAnti_lamT {lam : Fin n → ℝ} (hlam : StrictAnti lam) (t : ℕ) : StrictAnti (lamT lam t) := by
  intro a b hab
  rw [lamT_apply, lamT_apply]
  have h1 := hlam hab
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast (show (a : ℕ) < b from hab)
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  nlinarith

theorem isHCParam_lamT {lam : Fin n → ℝ} (hlam : IsHCParam lam) (t : ℕ) : IsHCParam (lamT lam t) := by
  refine ⟨strictAnti_lamT hlam.1 t, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hlam.2 a
  refine ⟨m + (t : ℤ) * ((n : ℤ) - 1 - ((a : ℕ) : ℤ)), ?_⟩
  rw [lamT_apply]
  push_cast
  linear_combination hm

theorem gap_lamT {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) (t : ℕ) : GapAtLeast ε (lamT lam t) (h + t) := by
  intro a b hab
  have hne : a ≠ b := fun e => hab (by rw [e])
  have hg := hgap a b hab
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  rw [lamT_sub]
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have hl := hlam h1
    have hab' : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast (show (a : ℕ) + 1 ≤ b from h1)
    rw [abs_of_pos (sub_pos.mpr hl)] at hg
    exact le_abs.mpr (Or.inl (by nlinarith))
  · have hl := hlam h1
    have hab' : ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ) := by exact_mod_cast (show (b : ℕ) + 1 ≤ a from h1)
    rw [abs_of_neg (sub_neg.mpr hl)] at hg
    exact le_abs.mpr (Or.inr (by nlinarith))

theorem lowK_lamT (ε : Fin n → Bool) (lam : Fin n → ℝ) (t : ℕ) :
    lowK ε (lamT lam t) = lowK ε lam + (t : ℝ) • Dvec n := by
  unfold lowK lamT
  abel

theorem vand_pos {lam : Fin n → ℝ} (hlam : StrictAnti lam) : 0 < Vand lam := by
  unfold Vand
  refine Finset.prod_pos (fun a _ => Finset.prod_pos (fun b hb => ?_))
  have hab : a < b := (Finset.mem_filter.mp hb).2
  exact sub_pos.mpr (hlam hab)

theorem ratioV_eq_vand {μ : Fin n → ℝ} (hμ : StrictAnti μ) (s : Fin n) :
    ratioV μ s = Vand (μ + Pi.single s 1) / Vand μ := by
  have hne : ∀ a b : Fin n, a ≠ b → μ a - μ b ≠ 0 := fun a b h => sub_ne_zero.mpr (hμ.injective.ne h)
  have hV : Vand μ ≠ 0 := (vand_pos hμ).ne'
  have hfac : ∀ a ∈ (univ : Finset (Fin n)), ∀ b ∈ univ.filter (fun b : Fin n => a < b),
      (μ + Pi.single s (1 : ℝ) : Fin n → ℝ) a - (μ + Pi.single s (1 : ℝ) : Fin n → ℝ) b =
        (μ a - μ b) * ((if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1) *
          (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1)) := by
    intro a _ b hb
    have hab : a < b := (Finset.mem_filter.mp hb).2
    have hab' : a ≠ b := ne_of_lt hab
    by_cases ha : a = s
    · subst ha
      have h1 : μ a - μ b ≠ 0 := hne a b hab'
      rw [if_pos rfl, if_neg hab'.symm, mul_one]
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab'.symm, add_zero]
      field_simp <;> ring
    · by_cases hb' : b = s
      · subst hb'
        have h2 : μ b - μ a ≠ 0 := hne b a hab'.symm
        rw [if_neg ha, if_pos rfl, one_mul]
        simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne ha, add_zero]
        field_simp <;> ring
      · rw [if_neg ha, if_neg hb', mul_one, mul_one]
        simp only [Pi.add_apply, Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb', add_zero]
  rw [eq_div_iff hV]
  have hsplit : Vand (μ + Pi.single s 1) = Vand μ *
      ((∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1)) *
        ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1)) := by
    unfold Vand
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun a ha => ?_)
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun b hb => hfac a ha b hb)
  have hA : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if a = s then (μ s + 1 - μ b) / (μ s - μ b) else 1)) =
        ∏ b ∈ univ.filter (fun b : Fin n => s < b), (μ s + 1 - μ b) / (μ s - μ b) := by
    rw [Finset.prod_eq_single s]
    · exact Finset.prod_congr rfl (fun b _ => if_pos rfl)
    · intro a _ ha
      exact Finset.prod_eq_one (fun b _ => if_neg ha)
    · intro h
      exact absurd (Finset.mem_univ s) h
  have hB : (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b),
          (if b = s then (μ s + 1 - μ a) / (μ s - μ a) else 1)) =
        ∏ a ∈ univ.filter (fun a : Fin n => a < s), (μ s + 1 - μ a) / (μ s - μ a) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [Finset.prod_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsplit, hA, hB]
  unfold ratioV
  rw [← Finset.prod_filter_mul_prod_filter_not (univ.erase s) (fun x => x < s)]
  have e1 : (univ.erase s).filter (fun x => x < s) = univ.filter (fun x : Fin n => x < s) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
  have e2 : (univ.erase s).filter (fun x => ¬ x < s) = univ.filter (fun x : Fin n => s < x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h.2 (Ne.symm h.1), fun h => ⟨ne_of_gt h, le_of_lt h⟩⟩
  rw [e1, e2]
  ring

theorem prod_sub_lt_eq_factorial (b : Fin n) :
    ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = ((b : ℕ).factorial : ℝ) := by
  have gen : ∀ m : ℕ, ∏ k ∈ range m, ((m : ℝ) - (k : ℝ)) = (m.factorial : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ', Nat.factorial_succ, Nat.cast_mul, ← ih]
      have e : ∀ k ∈ range m, (((m + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) = (m : ℝ) - (k : ℝ) := by
        intro k _
        push_cast
        ring
      rw [Finset.prod_congr rfl e]
      push_cast
      ring
  have h1 : ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ k ∈ range (b : ℕ), (((b : ℕ) : ℝ) - (k : ℝ)) := by
    apply Finset.prod_nbij (fun a : Fin n => (a : ℕ))
    · intro a ha
      exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
    · intro a _ a' _ h
      exact Fin.ext h
    · intro k hk
      have hk' : k < (b : ℕ) := Finset.mem_range.mp hk
      refine ⟨⟨k, lt_trans hk' b.isLt⟩, ?_, rfl⟩
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      exact hk'
    · intro a _
      rfl
  rw [h1, gen]

theorem prod_pairs_eq_factorial (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range n, (i.factorial : ℝ) := by
  rw [Finset.prod_comm' (t' := univ) (s' := fun b => univ.filter (fun a : Fin n => a < b))
    (by intro a b; simp)]
  rw [Finset.prod_congr rfl (fun b _ => prod_sub_lt_eq_factorial b)]
  exact Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) n

theorem dimVlam_eq_vand {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    dimVlam lam = Vand lam / ∏ i ∈ range n, (i.factorial : ℝ) := by
  unfold dimVlam Vand
  rw [prod_pairs_eq_factorial]
  congr 1
  refine Finset.prod_congr rfl (fun a _ => Finset.prod_congr rfl (fun b hb => ?_))
  exact abs_of_pos (sub_pos.mpr (hlam (Finset.mem_filter.mp hb).2))

end ReciprocityTheory.ChartRestriction.DS

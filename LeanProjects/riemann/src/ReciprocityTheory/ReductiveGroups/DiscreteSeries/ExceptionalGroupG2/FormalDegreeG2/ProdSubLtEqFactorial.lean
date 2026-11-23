import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdDefs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem sCoef_lamT (lam : Fin n → ℝ) (t : ℕ) {i : ℕ} (hi : i + 1 < n) :
    sCoef (lamT lam t) i = sCoef lam i + t := by
  simp only [sCoef, dif_pos hi, lamT, Dvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem sCoef_zero_of (i : ℕ) (hi : i + 1 < n) : sCoef (0 : Fin n → ℝ) i = 1 := by
  simp [sCoef, dif_pos hi]

theorem ph_lamT (lam : Fin n → ℝ) (t : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Ph (lamT lam t) X = Ph lam X + (t : ℝ) * Ph (0 : Fin n → ℝ) X := by
  simp only [Ph, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i + 1 < n := by simp at hi; omega
  rw [sCoef_lamT lam t hi', sCoef_zero_of i hi']
  ring

theorem dvec_antitone : Antitone (Dvec n) := by
  intro a b hab
  simp only [Dvec]
  have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

theorem lamT_apply (lam : Fin n → ℝ) (t : ℕ) (a : Fin n) :
    lamT lam t a = lam a + (t : ℝ) * ((n : ℝ) - 1 - ((a : ℕ) : ℝ)) := by
  simp [lamT, Dvec]

theorem lamT_sub (lam : Fin n → ℝ) (t : ℕ) (a b : Fin n) :
    lamT lam t a - lamT lam t b = (lam a - lam b) + (t : ℝ) * (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  rw [lamT_apply, lamT_apply]; ring

theorem strictAnti_lamT {lam : Fin n → ℝ} (hlam : StrictAnti lam) (t : ℕ) : StrictAnti (lamT lam t) := by
  intro a b hab
  have h1 := hlam hab
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have h3 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have := lamT_sub lam t b a
  nlinarith

theorem isHCParam_lamT {lam : Fin n → ℝ} (hlam : IsHCParam lam) (t : ℕ) : IsHCParam (lamT lam t) := by
  refine ⟨strictAnti_lamT hlam.1 t, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hlam.2 a
  have ha : (a : ℕ) + 1 ≤ n := a.2
  refine ⟨m + (t : ℤ) * ((n : ℤ) - 1 - (a : ℤ)), ?_⟩
  rw [lamT_apply]
  push_cast
  linarith

theorem gap_lamT {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h) (t : ℕ) : GapAtLeast ε (lamT lam t) (h + t) := by
  intro a b hab
  have hg := hgap a b hab
  have hne : a ≠ b := fun e => hab (by rw [e])
  have h3 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := hlam hlt
    have h2 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [abs_of_pos (sub_pos.2 h1)] at hg
    rw [lamT_sub, abs_of_pos (by nlinarith)]
    nlinarith
  · have h1 := hlam hlt
    have h2 : ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ) := by exact_mod_cast hlt
    rw [abs_of_neg (sub_neg.2 h1)] at hg
    rw [lamT_sub, abs_of_neg (by nlinarith)]
    nlinarith

theorem lowK_lamT (ε : Fin n → Bool) (lam : Fin n → ℝ) (t : ℕ) :
    lowK ε (lamT lam t) = lowK ε lam + (t : ℝ) • Dvec n := by
  simp only [lowK, lamT]
  abel

theorem vand_pos {lam : Fin n → ℝ} (hlam : StrictAnti lam) : 0 < Vand lam := by
  unfold Vand
  refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact sub_pos.2 (hlam hb)

theorem ratioV_eq_vand {μ : Fin n → ℝ} (hμ : StrictAnti μ) (s : Fin n) :
    ratioV μ s = Vand (μ + Pi.single s 1) / Vand μ := by
  set ν : Fin n → ℝ := μ + Pi.single s 1 with hν
  set r : Fin n → Fin n → ℝ := fun a b => (ν a - ν b) / (μ a - μ b) with hr
  have hsplit : Vand ν / Vand μ = ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), r a b := by
    simp only [Vand, hr, Finset.prod_div_distrib]
  have hr1 : ∀ a b : Fin n, a ≠ s → b ≠ s → a < b → r a b = 1 := by
    intro a b ha hb hab
    have : μ a - μ b ≠ 0 := (sub_pos.2 (hμ hab)).ne'
    simp only [hr, hν, Pi.add_apply, Pi.single_apply, if_neg ha, if_neg hb, add_zero]
    exact div_self this
  have hin : ∀ a : Fin n, a ≠ s →
      ∏ b ∈ univ.filter (fun b : Fin n => a < b), r a b = if a < s then r a s else 1 := by
    intro a ha
    split_ifs with has
    · rw [Finset.prod_eq_single_of_mem s (by simp [has])]
      intro b hb hbs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact hr1 a b ha hbs hb
    · refine Finset.prod_eq_one fun b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hbs : b ≠ s := fun e => has (e ▸ hb)
      exact hr1 a b ha hbs hb
  rw [hsplit, ← Finset.mul_prod_erase univ _ (mem_univ s)]
  rw [Finset.prod_congr rfl (fun a ha => hin a (Finset.ne_of_mem_erase ha))]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
  have hfac : ∀ s' ∈ univ.erase s, (μ s + 1 - μ s') / (μ s - μ s') =
      if s < s' then r s s' else r s' s := by
    intro s' hs'
    have hne : s' ≠ s := Finset.ne_of_mem_erase hs'
    have hne' : μ s - μ s' ≠ 0 := sub_ne_zero.2 (hμ.injective.ne hne.symm)
    have hne'' : μ s' - μ s ≠ 0 := sub_ne_zero.2 (hμ.injective.ne hne)
    split_ifs with h
    · simp only [hr, hν, Pi.add_apply, Pi.single_apply, if_neg hne, ↓reduceIte]
      ring_nf
    · simp only [hr, hν, Pi.add_apply, Pi.single_apply, if_neg hne, ↓reduceIte, add_zero]
      rw [div_eq_div_iff hne' hne'']
      ring
  unfold ratioV
  rw [Finset.prod_congr rfl hfac, Finset.prod_ite]
  have e1 : (univ.erase s).filter (fun s' => s < s') = univ.filter (fun b : Fin n => s < b) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨ne_of_gt h, h⟩
  have e2 : (univ.erase s).filter (fun s' => ¬ s < s') = (univ.erase s).filter (fun a : Fin n => a < s) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, lt_of_le_of_ne (not_lt.1 h2) h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, not_lt.2 h2.le⟩
  rw [e1, e2]

theorem prod_sub_lt_eq_factorial (b : Fin n) :
    ∏ a ∈ univ.filter (fun a : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = ((b : ℕ).factorial : ℝ) := by
  rw [Finset.prod_filter]
  simp_rw [Fin.lt_def]
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < (b : ℕ) then (((b : ℕ) : ℝ) - (i : ℝ)) else 1) n]
  rw [← Finset.prod_filter]
  have hb : (b : ℕ) < n := b.2
  have e : (range n).filter (fun i => i < (b : ℕ)) = range (b : ℕ) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [e, ← Finset.prod_range_reflect]
  have : ∀ j ∈ range (b : ℕ), (((b : ℕ) : ℝ) - (((b : ℕ) - 1 - j : ℕ) : ℝ)) = ((j + 1 : ℕ) : ℝ) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have h1 : (b : ℕ) - 1 - j + (j + 1) = (b : ℕ) := by omega
    have h2 : ((((b : ℕ) - 1 - j : ℕ) : ℝ)) + ((j + 1 : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  rw [Finset.prod_congr rfl this, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]

theorem prod_pairs_eq_factorial (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range n, (i.factorial : ℝ) := by
  rw [Finset.prod_comm' (t' := univ) (s' := fun b => univ.filter (fun a : Fin n => a < b))
    (fun x y => by simp)]
  simp_rw [prod_sub_lt_eq_factorial]
  exact Fin.prod_univ_eq_prod_range (fun i => (i.factorial : ℝ)) n

theorem dimVlam_eq_vand {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    dimVlam lam = Vand lam / ∏ i ∈ range n, (i.factorial : ℝ) := by
  unfold dimVlam Vand
  rw [prod_pairs_eq_factorial]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact abs_of_pos (sub_pos.2 (hlam hb))

end ReciprocityTheory.ChartRestriction.DS.G2

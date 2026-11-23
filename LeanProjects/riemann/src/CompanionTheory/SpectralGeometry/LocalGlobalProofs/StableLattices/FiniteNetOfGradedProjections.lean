import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose

open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

namespace GlobalTheory.CompanionTheory.UGeo.GradNet

variable {n : ℕ}

theorem norm_entry_sq_le_hs (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖M i j‖ ^ 2 ≤ Formalism.REAL.hs M := by
  unfold Formalism.REAL.hs
  calc ‖M i j‖ ^ 2 ≤ ∑ b, ‖M i b‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ‖M i b‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ a, ∑ b, ‖M a b‖ ^ 2 :=
        Finset.single_le_sum (f := fun a => ∑ b, ‖M a b‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem norm_entry_le {M : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.hs M ≤ n) (i j : Fin n) :
    ‖M i j‖ ≤ (n : ℝ) + 1 := by
  have h1 := (norm_entry_sq_le_hs M i j).trans h
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_contra hc
  push_neg at hc
  nlinarith

theorem hs_le_quarter {M : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ i j, ‖M i j‖ < 1 / (2 * ((n : ℝ) + 1))) : Formalism.REAL.hs M ≤ 1 / 4 := by
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : Formalism.REAL.hs M ≤ ∑ _a : Fin n, ∑ _b : Fin n, (1 / (2 * ((n : ℝ) + 1))) ^ 2 := by
    unfold Formalism.REAL.hs
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      pow_le_pow_left₀ (norm_nonneg _) (h a b).le 2
  have e : ∑ _a : Fin n, ∑ _b : Fin n, (1 / (2 * ((n : ℝ) + 1))) ^ 2
      = ((n : ℝ) * (1 / (2 * ((n : ℝ) + 1)))) ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have h2 : (n : ℝ) * (1 / (2 * ((n : ℝ) + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have h3 : 0 ≤ (n : ℝ) * (1 / (2 * ((n : ℝ) + 1))) := by positivity
  rw [e] at h1
  nlinarith

theorem exists_net (n : ℕ) (ε : Fin n → Bool) :
    ∃ (m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ j, IsGrad ε (A j)) ∧
      ∀ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' →
        ∃ j, Formalism.REAL.hs (Pm (A j) - Pm A') ≤ 1 / 4 ∧ Formalism.REAL.hs (Pp (A j) - Pp A') ≤ 1 / 4 := by
  classical
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  let f : Matrix (Fin n) (Fin n) ℂ → (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) :=
    fun A => (fun i j => Pm A i j, fun i j => Pp A i j)
  have hb : Bornology.IsBounded (f '' {A | IsGrad ε A}) := by
    refine (Metric.isBounded_closedBall
      (x := (0 : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ))) (r := (n : ℝ) + 1)).subset ?_
    rintro _ ⟨A, hA, rfl⟩
    have hA' : IsGrad ε A := hA
    have hm := hs_proj_le (Pm_conj hA') (Pm_idem hA')
    have hp := hs_proj_le (Pp_conj hA') (Pp_idem hA')
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    refine max_le ?_ ?_
    · exact (pi_norm_le_iff_of_nonneg hn).2 fun i =>
        (pi_norm_le_iff_of_nonneg hn).2 fun j => norm_entry_le hm i j
    · exact (pi_norm_le_iff_of_nonneg hn).2 fun i =>
        (pi_norm_le_iff_of_nonneg hn).2 fun j => norm_entry_le hp i j
  have hr : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  obtain ⟨t, hts, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded
    ((Bornology.IsBounded.isCompact_closure hb).totallyBounded.subset subset_closure) _ hr
  have hch : ∀ y : t, ∃ A, IsGrad ε A ∧ f A = y := fun y => by
    obtain ⟨A, hA, e⟩ := hts y.2
    exact ⟨A, hA, e⟩
  choose a ha hfa using hch
  haveI : Fintype t := htf.fintype
  let e := Fintype.equivFin t
  refine ⟨Fintype.card t, fun j => a (e.symm j), fun j => ha _, fun A' hA' => ?_⟩
  have hmem : f A' ∈ ⋃ y ∈ t, Metric.ball y (1 / (2 * ((n : ℝ) + 1))) := hcov ⟨A', hA', rfl⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hmem
  obtain ⟨y, hy, hd⟩ := hmem
  have hd' : dist (f (a (e.symm (e ⟨y, hy⟩)))) (f A') < 1 / (2 * ((n : ℝ) + 1)) := by
    rw [Equiv.symm_apply_apply, hfa, dist_comm]
    exact hd
  rw [Prod.dist_eq, max_lt_iff] at hd'
  refine ⟨e ⟨y, hy⟩, hs_le_quarter fun i j => ?_, hs_le_quarter fun i j => ?_⟩
  · have h1 := (dist_le_pi_dist (f (a (e.symm (e ⟨y, hy⟩)))).1 (f A').1 i).trans_lt hd'.1
    have h2 := (dist_le_pi_dist _ _ j).trans_lt h1
    simpa [f, dist_eq_norm] using h2
  · have h1 := (dist_le_pi_dist (f (a (e.symm (e ⟨y, hy⟩)))).2 (f A').2 i).trans_lt hd'.2
    have h2 := (dist_le_pi_dist _ _ j).trans_lt h1
    simpa [f, dist_eq_norm] using h2

end GlobalTheory.CompanionTheory.UGeo.GradNet

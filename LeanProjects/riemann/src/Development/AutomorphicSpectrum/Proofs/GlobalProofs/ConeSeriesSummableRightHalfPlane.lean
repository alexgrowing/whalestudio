import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem summable_prod_fin {f : ℕ → ℝ} (hf : Summable f) (h0 : ∀ n, 0 ≤ f n) (r : ℕ) :
    Summable (fun m : Fin r → ℕ => ∏ i, f (m i)) := by
  induction r with
  | zero => exact Summable.of_finite
  | succ r ih =>
    have h2 := Summable.mul_of_nonneg hf ih (fun n => h0 n)
      (fun m => Finset.prod_nonneg fun i _ => h0 (m i))
    rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).summable_iff]
    convert h2 using 1
    funext x
    simp [Fin.consEquiv, Fin.prod_univ_succ]

private theorem exists_pos_lower_bound_of_forall_pos {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ)
    (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) :
    ∃ c : ℝ, 0 < c ∧ (∀ j, c ≤ b j) ∧ ∀ j i, c ≤ a j i := by
  classical
  let T : Finset ℝ := Finset.univ.image b ∪ Finset.univ.image (fun p : ι × Fin r => a p.1 p.2)
  by_cases hT : T.Nonempty
  · refine ⟨T.min' hT, ?_, fun j => T.min'_le _ ?_, fun j i => T.min'_le _ ?_⟩
    · have h := T.min'_mem hT
      simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
      rcases h with ⟨j, hj⟩ | ⟨⟨j, i⟩, hj⟩
      · rw [← hj]; exact hb j
      · rw [← hj]; exact ha j i
    · simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl ⟨j, rfl⟩
    · simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨(j, i), rfl⟩
  · refine ⟨1, one_pos, fun j => ?_, fun j i => ?_⟩
    · exact absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT
    · exact absurd ⟨b j, by simp only [T, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]; exact Or.inl ⟨j, rfl⟩⟩ hT

theorem coneTerm_summable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ),
    r ≤ Fintype.card ι → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ s : ℂ, 1 < s.re →
    Summable (coneTerm a b s) := by
  intro ι _ r a b hr ha hb s hs
  obtain ⟨c, hc0, hcb, hca⟩ := exists_pos_lower_bound_of_forall_pos a b ha hb
  have hσ0 : 0 < s.re := by linarith
  have hf : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-s.re)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hC : 0 ≤ (c ^ (-s.re)) ^ Fintype.card ι := pow_nonneg (Real.rpow_nonneg hc0.le _) _
  have hg := (summable_prod_fin hf (fun k => Real.rpow_nonneg (by positivity) _) r).mul_left
    ((c ^ (-s.re)) ^ Fintype.card ι)
  have key : ∀ {x y : ℝ}, 0 < x → x ≤ y → y ^ (-s.re) ≤ x ^ (-s.re) := fun hx hxy => by
    rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
    exact inv_anti₀ (Real.rpow_pos_of_pos hx _) (Real.rpow_le_rpow hx.le hxy hσ0.le)
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hg)
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ i, (m i : ℝ) := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, (m i : ℝ) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (m i))
  have hS1 : 1 ≤ S := by rw [hSdef]; linarith
  have hS0 : 0 < S := by linarith
  have hL : ∀ j, c * S ≤ b j + ∑ i, a j i * (m i : ℝ) := by
    intro j
    rw [hSdef, mul_add, mul_one, Finset.mul_sum]
    apply add_le_add (hcb j)
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hca j i) (Nat.cast_nonneg _)
  have hLpos : ∀ j, 0 < b j + ∑ i, a j i * (m i : ℝ) := fun j => lt_of_lt_of_le (mul_pos hc0 hS0) (hL j)
  have hv1 : S ^ (-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hS1 (by linarith)
  have hv0 : 0 ≤ S ^ (-s.re) := Real.rpow_nonneg hS0.le _
  calc ‖coneTerm a b s m‖ = ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ (-s.re) := by
        rw [coneTerm, norm_prod]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hLpos j), Complex.neg_re]
    _ ≤ ∏ _j : ι, (c * S) ^ (-s.re) :=
        Finset.prod_le_prod (fun j _ => Real.rpow_nonneg (hLpos j).le _)
          (fun j _ => key (mul_pos hc0 hS0) (hL j))
    _ = (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ, Real.mul_rpow hc0.le hS0.le, mul_pow]
    _ ≤ (c ^ (-s.re)) ^ Fintype.card ι * (S ^ (-s.re)) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hv0 hv1 hr) hC
    _ = (c ^ (-s.re)) ^ Fintype.card ι * ∏ _i : Fin r, S ^ (-s.re) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (c ^ (-s.re)) ^ Fintype.card ι * ∏ i, ((m i : ℝ) + 1) ^ (-s.re) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.prod_le_prod (fun i _ => hv0)
        intro i _
        apply key (by positivity)
        have hi : (m i : ℝ) ≤ ∑ k, (m k : ℝ) :=
          Finset.single_le_sum (fun k _ => Nat.cast_nonneg (m k)) (Finset.mem_univ i)
        rw [hSdef]
        linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

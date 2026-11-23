import Mathlib

open Polynomial

namespace GlobalTheory.TranslateSpan

open Classical in

noncomputable def weight (p : ℂ[X]) : ℕ := if p = 0 then 0 else p.natDegree + 1

noncomputable def diff (a b r : ℂ) (p : ℂ[X]) : ℂ[X] := C a * taylor r p - C b * p

lemma natDegree_diff_le (a b r : ℂ) (p : ℂ[X]) : (diff a b r p).natDegree ≤ p.natDegree := by
  unfold diff
  refine (natDegree_sub_le _ _).trans (max_le ?_ (natDegree_C_mul_le _ _))
  exact (natDegree_C_mul_le _ _).trans (natDegree_taylor _ _).le

lemma coeff_diff (a b r : ℂ) (p : ℂ[X]) :
    (diff a b r p).coeff p.natDegree = (a - b) * p.leadingCoeff := by
  unfold diff
  rw [coeff_sub, coeff_C_mul, coeff_C_mul, coeff_taylor_natDegree, coeff_natDegree]
  ring

lemma weight_diff_le (a b r : ℂ) (p : ℂ[X]) : weight (diff a b r p) ≤ weight p := by
  by_cases hp : p = 0
  · subst hp; simp [weight, diff]
  · have := natDegree_diff_le a b r p
    unfold weight
    split_ifs <;> omega

lemma weight_diff_lt (a r : ℂ) (p : ℂ[X]) (hp : p ≠ 0) : weight (diff a a r p) < weight p := by
  have h1 := natDegree_diff_le a a r p
  have h2 := coeff_diff a a r p
  rw [sub_self, zero_mul] at h2
  unfold weight
  rw [if_neg hp]
  split_ifs with h
  · omega
  · have : (diff a a r p).natDegree ≠ p.natDegree := by
      intro e
      rw [← e, coeff_natDegree, leadingCoeff_eq_zero] at h2
      exact h h2
    omega

lemma diff_ne_zero (a b r : ℂ) (p : ℂ[X]) (hab : a ≠ b) (hp : p ≠ 0) : diff a b r p ≠ 0 := by
  intro h
  have h2 := coeff_diff a b r p
  rw [h, coeff_zero] at h2
  exact mul_ne_zero (sub_ne_zero.2 hab) (leadingCoeff_ne_zero.2 hp) h2.symm

lemma diff_self_ne_zero (a r : ℂ) (p : ℂ[X]) (ha : a ≠ 0) (hr : r ≠ 0) (hp : p.natDegree ≠ 0) :
    diff a a r p ≠ 0 := by
  intro h
  have hx : ∀ x, p.eval (x + r) = p.eval x := by
    intro x
    have := congrArg (eval x) h
    simp only [diff, eval_sub, eval_mul, eval_C, taylor_eval, eval_zero] at this
    rw [← mul_sub, mul_eq_zero, sub_eq_zero] at this
    exact this.resolve_left ha
  have hn : ∀ n : ℕ, p.eval ((n : ℂ) * r) = p.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [← ih, ← hx (n * r)]; congr 1; push_cast; ring
  have hz : p - C (p.eval 0) = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ) * r) ?_ ?_
    · intro m n hmn
      exact_mod_cast mul_right_cancel₀ hr hmn
    · intro n
      simp [hn n]
  apply hp
  rw [sub_eq_zero.1 hz, natDegree_C]

section
variable {G : Type} [CommGroup G] (L : G → ℝ) {ι : Type} [Fintype ι] (χ : ι → G →* ℂˣ)

noncomputable def spanTr (P : ι → ℂ[X]) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (Set.range fun s : G => fun t : G =>
    ∑ i, (P i).eval ((L (s * t) : ℝ) : ℂ) * ((χ i (s * t) : ℂˣ) : ℂ))

lemma spanTr_diff_le (hL : ∀ x y, L (x * y) = L x + L y) (P : ι → ℂ[X]) (s : G) (a : ℂ) :
    spanTr L χ (fun i => diff (χ i s : ℂˣ) a (L s) (P i)) ≤ spanTr L χ P := by
  refine Submodule.span_le.2 (Set.range_subset_iff.2 fun s' => ?_)
  have h1 : (fun t : G => ∑ i, (P i).eval ((L ((s * s') * t) : ℝ) : ℂ) *
      ((χ i ((s * s') * t) : ℂˣ) : ℂ)) ∈ spanTr L χ P := Submodule.subset_span ⟨s * s', rfl⟩
  have h2 : (fun t : G => ∑ i, (P i).eval ((L (s' * t) : ℝ) : ℂ) *
      ((χ i (s' * t) : ℂˣ) : ℂ)) ∈ spanTr L χ P := Submodule.subset_span ⟨s', rfl⟩
  have h3 := Submodule.sub_mem _ h1 (Submodule.smul_mem _ a h2)
  rw [SetLike.mem_coe]
  convert h3 using 1
  funext t
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc s s' t, hL s (s' * t), map_mul (χ i) s]
  simp only [diff, eval_sub, eval_mul, eval_C, taylor_eval, Units.val_mul, Complex.ofReal_add]
  rw [add_comm ((L s : ℝ) : ℂ)]
  ring

theorem mem_spanTr (hL : ∀ x y, L (x * y) = L x + L y) (h0 : ∃ t, L t ≠ 0)
    (hχ : Function.Injective χ) (i₀ : ι) (n : ℕ) :
    ∀ P : ι → ℂ[X], ∑ i, weight (P i) = n → P i₀ ≠ 0 →
      (fun t => ((χ i₀ t : ℂˣ) : ℂ)) ∈ spanTr L χ P := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hn hP
  have step : ∀ (s : G) (i₁ : ι), P i₁ ≠ 0 →
      diff (χ i₀ s : ℂˣ) (χ i₁ s : ℂˣ) (L s) (P i₀) ≠ 0 →
      (fun t => ((χ i₀ t : ℂˣ) : ℂ)) ∈ spanTr L χ P := by
    intro s i₁ h1 h2
    refine spanTr_diff_le L χ hL P s (χ i₁ s : ℂˣ) (ih _ ?_ _ rfl h2)
    rw [← hn]
    exact Finset.sum_lt_sum (fun i _ => weight_diff_le _ _ _ _)
      ⟨i₁, Finset.mem_univ _, weight_diff_lt _ _ _ h1⟩
  by_cases hA : ∃ i₁, i₁ ≠ i₀ ∧ P i₁ ≠ 0
  · obtain ⟨i₁, hi, h1⟩ := hA
    obtain ⟨s, hs⟩ : ∃ s, χ i₀ s ≠ χ i₁ s := by
      by_contra hc
      push Not at hc
      exact hi (hχ (MonoidHom.ext hc)).symm
    exact step s i₁ h1 (diff_ne_zero _ _ _ _ (fun e => hs (Units.ext e)) hP)
  · push Not at hA
    by_cases hd : (P i₀).natDegree = 0
    · obtain ⟨c, hc⟩ : ∃ c, P i₀ = C c := ⟨_, eq_C_of_natDegree_eq_zero hd⟩
      have hc0 : c ≠ 0 := by rintro rfl; exact hP (by simpa using hc)
      have h2 : (fun t : G => ∑ i, (P i).eval ((L (1 * t) : ℝ) : ℂ) *
        ((χ i (1 * t) : ℂˣ) : ℂ)) ∈ spanTr L χ P := Submodule.subset_span ⟨1, rfl⟩
      convert Submodule.smul_mem _ c⁻¹ h2 using 1
      funext t
      simp only [Pi.smul_apply, smul_eq_mul, one_mul]
      rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hA i hi]) (by simp), hc, eval_C,
        ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    · obtain ⟨s, hs⟩ := h0
      exact step s i₀ hP (diff_self_ne_zero _ _ _ (Units.ne_zero _) (by exact_mod_cast hs) hd)
end

end GlobalTheory.TranslateSpan

namespace GlobalTheory

theorem character_mem_span_translates :
    ∀ (G : Type) [CommGroup G] (L : G → ℝ), (∀ x y, L (x * y) = L x + L y) → (∃ t, L t ≠ 0) →
    ∀ (ι : Type) [Fintype ι] (χ : ι → G →* ℂˣ), Function.Injective χ →
    ∀ (P : ι → ℂ[X]) (i₀ : ι), P i₀ ≠ 0 →
      (fun t => ((χ i₀ t : ℂˣ) : ℂ)) ∈ Submodule.span ℂ (Set.range fun s : G => fun t : G =>
        ∑ i, (P i).eval ((L (s * t) : ℝ) : ℂ) * ((χ i (s * t) : ℂˣ) : ℂ)) :=
  fun _ _ L hL h0 _ _ χ hχ P i₀ hP =>
    TranslateSpan.mem_spanTr L χ hL h0 hχ i₀ _ P rfl hP

end GlobalTheory

import Formalism.HermitianCurvature.LevelRecursionCondNeeded

namespace Formalism.FourierDecayAlt.P.SchurNormSquareBounds

open Finset

lemma norm_sq_sum_le {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type}
    [DecidableEq ι] (T : Finset ι) (V : ι → H) :
    ‖∑ t ∈ T, V t‖ ^ 2 ≤
      (∑ t ∈ T, ‖V t‖ ^ 2) + ∑ t ∈ T, ∑ t' ∈ T.erase t, ‖inner ℂ (V t) (V t')‖ := by
  have h1 : ‖∑ t ∈ T, V t‖ ^ 2 = ∑ t ∈ T, ∑ t' ∈ T, (inner ℂ (V t) (V t')).re := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
    simp only [inner_sum]
    simp
  rw [h1, ← sum_add_distrib]
  refine sum_le_sum fun t ht => ?_
  rw [← add_sum_erase T _ ht]
  refine add_le_add ?_ (sum_le_sum fun t' _ => ?_)
  · rw [norm_sq_eq_re_inner (𝕜 := ℂ)]; simp
  · exact (le_abs_self _).trans (Complex.abs_re_le_norm _)

lemma row_le {G ι : Type} [AddCommGroup G] [DecidableEq ι] (La : AddSubgroup G) (T : Finset ι)
    (τ : ι → G) (ψ : G → ℝ) (ε : ℝ) (hinj : Set.InjOn τ T)
    (hco : ∀ t ∈ T, ∀ t' ∈ T, τ t - τ t' ∈ La)
    (hS : ∀ S : Finset G, (∀ l ∈ S, l ∈ La ∧ l ≠ 0) → ∑ l ∈ S, ψ l ≤ ε) (t : ι) (ht : t ∈ T) :
    ∑ t' ∈ T.erase t, ψ (τ t - τ t') ≤ ε ∧ ∑ t' ∈ T.erase t, ψ (τ t' - τ t) ≤ ε := by
  classical
  constructor
  · have := hS ((T.erase t).image fun t' => τ t - τ t') (by
      intro l hl
      obtain ⟨t', ht', rfl⟩ := mem_image.1 hl
      obtain ⟨hne, ht'T⟩ := mem_erase.1 ht'
      exact ⟨hco t ht t' ht'T, fun h => hne (hinj ht'T ht (sub_eq_zero.1 h).symm)⟩)
    rwa [sum_image] at this
    intro x hx y hy hxy
    exact hinj (mem_erase.1 hx).2 (mem_erase.1 hy).2 (sub_right_injective hxy)
  · have := hS ((T.erase t).image fun t' => τ t' - τ t) (by
      intro l hl
      obtain ⟨t', ht', rfl⟩ := mem_image.1 hl
      obtain ⟨hne, ht'T⟩ := mem_erase.1 ht'
      exact ⟨hco t' ht'T t ht, fun h => hne (hinj ht'T ht (sub_eq_zero.1 h))⟩)
    rwa [sum_image] at this
    intro x hx y hy hxy
    exact hinj (mem_erase.1 hx).2 (mem_erase.1 hy).2 (sub_left_injective hxy)

end Formalism.FourierDecayAlt.P.SchurNormSquareBounds

namespace Formalism.FourierDecayAlt.P

open Finset SchurNormSquareBounds

theorem schur_two_factor_bound : Formalism.FourierDecayAlt.F7.SchurTwo := by
  classical
  intro H _ _ G _ La ι PP _ T τ V P φ a b ε hinj hco hφ hS hab hV
  refine (norm_sq_sum_le T V).trans (add_le_add le_rfl ?_)

  have step1 : ∑ t ∈ T, ∑ t' ∈ T.erase t, ‖inner ℂ (V t) (V t')‖ ≤
      ∑ t ∈ T, ∑ t' ∈ T.erase t, ∑ p, φ p (τ t - τ t') * ((a p t + b p t') / 2) := by
    refine sum_le_sum fun t ht => sum_le_sum fun t' ht' => ?_
    obtain ⟨hne, ht'T⟩ := mem_erase.1 ht'
    refine (hV t ht t' ht'T (Ne.symm hne)).trans ?_
    refine single_le_sum (f := fun p => φ p (τ t - τ t') * ((a p t + b p t') / 2))
      (fun p _ => ?_) (mem_univ (P t t'))
    have h1 := hφ p _ (hco t ht t' ht'T)
    have h2 := (hab p t ht).1
    have h3 := (hab p t' ht'T).2
    positivity
  refine step1.trans ?_
  have step2 : ∑ t ∈ T, ∑ t' ∈ T.erase t, ∑ p, φ p (τ t - τ t') * ((a p t + b p t') / 2) =
      ∑ p, ((∑ t ∈ T, a p t / 2 * ∑ t' ∈ T.erase t, φ p (τ t - τ t')) +
        ∑ t' ∈ T, b p t' / 2 * ∑ t ∈ T.erase t', φ p (τ t - τ t')) := by
    have e1 : ∀ p, ∑ t' ∈ T, b p t' / 2 * ∑ t ∈ T.erase t', φ p (τ t - τ t') =
        ∑ t ∈ T, ∑ t' ∈ T.erase t, b p t' / 2 * φ p (τ t - τ t') := by
      intro p
      simp only [mul_sum]
      refine sum_comm' ?_
      intro x y
      simp only [mem_erase]
      constructor
      · rintro ⟨hx, hne, hy⟩; exact ⟨⟨hne.symm, hx⟩, hy⟩
      · rintro ⟨⟨hne, hx⟩, hy⟩; exact ⟨hx, hne.symm, hy⟩
    simp only [e1]
    simp only [mul_sum, ← sum_add_distrib]
    rw [sum_comm]
    refine sum_congr rfl fun t _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun t' _ => sum_congr rfl fun p _ => ?_
    ring
  rw [step2, mul_sum]
  refine sum_le_sum fun p _ => ?_
  have hA : ∑ t ∈ T, a p t / 2 * ∑ t' ∈ T.erase t, φ p (τ t - τ t') ≤ ∑ t ∈ T, a p t / 2 * ε :=
    sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
      (row_le La T τ (φ p) ε hinj hco (hS p) t ht).1 (by have := (hab p t ht).1; positivity)
  have hB : ∑ t' ∈ T, b p t' / 2 * ∑ t ∈ T.erase t', φ p (τ t - τ t') ≤ ∑ t ∈ T, b p t / 2 * ε :=
    sum_le_sum fun t ht => mul_le_mul_of_nonneg_left
      (row_le La T τ (φ p) ε hinj hco (hS p) t ht).2 (by have := (hab p t ht).2; positivity)
  refine (add_le_add hA hB).trans (le_of_eq ?_)
  rw [← sum_add_distrib, mul_sum]
  exact sum_congr rfl fun t _ => by ring

theorem schur_lattice_bound : Formalism.FourierDecayAlt.F7.SchurLattice := by
  classical
  intro H _ _ G _ La ι PP _ T τ V P φ a ε hinj hco hφ hS ha hV
  constructor
  · have := schur_two_factor_bound H G La ι PP T τ V P φ a a ε hinj hco hφ hS
      (fun p t ht => ⟨ha p t ht, ha p t ht⟩) hV
    refine this.trans (le_of_eq ?_)
    congr 2
    rw [sum_comm]
    exact sum_congr rfl fun t _ => sum_congr rfl fun p _ => by ring
  · intro f m hcard hε hm ham
    refine add_le_add le_rfl ?_
    have h1 : ∑ t ∈ T, ∑ p, a p t ≤ ∑ t ∈ T, (3 : ℝ) ^ f * m t := by
      refine sum_le_sum fun t ht => ?_
      calc ∑ p, a p t ≤ ∑ _p : PP, m t := sum_le_sum fun p _ => ham p t ht
        _ = (Fintype.card PP : ℝ) * m t := by simp
        _ ≤ (3 : ℝ) ^ f * m t := by
          refine mul_le_mul_of_nonneg_right ?_ (hm t ht)
          exact_mod_cast hcard
    calc ε * ∑ t ∈ T, ∑ p, a p t ≤ ε * ∑ t ∈ T, (3 : ℝ) ^ f * m t :=
          mul_le_mul_of_nonneg_left h1 hε
      _ = (3 : ℝ) ^ f * ε * ∑ t ∈ T, m t := by rw [← mul_sum]; ring

theorem schur_word_bound : Formalism.FourierDecayAlt.F7.SchurWords := by
  classical
  intro H _ _ G _ La ι PP Wd _ _ T τ V P φ θ θ' N ε D hinj hco hφ hS hθ hN hD hV
  have := schur_two_factor_bound H G La ι PP T τ V P φ (fun p t => ∑ w, θ p w * N w t)
    (fun p t => ∑ w, θ' p w * N w t) ε hinj hco hφ hS
    (fun p t ht => ⟨sum_nonneg fun w _ => mul_nonneg ((hθ p).1 w) (hN w t ht),
      sum_nonneg fun w _ => mul_nonneg ((hθ p).2.2.1 w) (hN w t ht)⟩) hV
  refine this.trans (add_le_add le_rfl ?_)

  have key : ∀ (ϑ : Wd → ℝ), (∀ w, 0 ≤ ϑ w) → ∑ w, ϑ w = 1 →
      ∑ t ∈ T, ∑ w, ϑ w * N w t ≤ D := by
    intro ϑ h0 h1
    rw [sum_comm]
    calc ∑ w, ∑ t ∈ T, ϑ w * N w t = ∑ w, ϑ w * ∑ t ∈ T, N w t := by simp only [mul_sum]
      _ ≤ ∑ w, ϑ w * D := sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hD w) (h0 w)
      _ = D := by rw [← sum_mul, h1, one_mul]
  rw [mul_sum]
  calc ∑ p, ε * ∑ t ∈ T, ((∑ w, θ p w * N w t) + ∑ w, θ' p w * N w t) / 2
      ≤ ∑ _p : PP, ε * D := by
        refine sum_le_sum fun p _ => ?_
        have hε : 0 ≤ ε := by simpa using hS p ∅ (by simp)
        refine mul_le_mul_of_nonneg_left ?_ hε
        have k1 := key (θ p) (hθ p).1 (hθ p).2.1
        have k2 := key (θ' p) (hθ p).2.2.1 (hθ p).2.2.2
        rw [← sum_div, sum_add_distrib]
        linarith
    _ = (Fintype.card PP : ℝ) * ε * D := by simp [mul_assoc]

end Formalism.FourierDecayAlt.P

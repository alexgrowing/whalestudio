import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDegLTGrowth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open GroundTheory.Heights₂.Heights.NumbersDVR

section Growth

variable {K : Type} [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in

theorem mixedDiff_of_fin_zero (bs : Fin 0 → K → ℤ) (f : (K → ℤ) → ℤ) : mixedDiff bs f = f := by
  simp [mixedDiff]

omit [Fintype K] [DecidableEq K] in

theorem mixedDiff_snoc_eq_diffStep {n : ℕ} (bs : Fin n → K → ℤ) (b : K → ℤ) (f : (K → ℤ) → ℤ) :
    mixedDiff (Fin.snoc bs b : Fin (n + 1) → K → ℤ) f = mixedDiff bs (diffStep b f) := by
  unfold mixedDiff
  rw [List.ofFn_succ']
  simp [List.concat_eq_append, List.foldr_append]

omit [Fintype K] [DecidableEq K] in

theorem degLT_diffStep_of_degLT_succ {n : ℕ} {f : (K → ℤ) → ℤ} (hf : DegLT f (n + 1)) (b : K → ℤ) :
    DegLT (diffStep b f) n := by
  intro bs
  have h := hf (Fin.snoc bs b : Fin (n + 1) → K → ℤ)
  rwa [mixedDiff_snoc_eq_diffStep] at h

omit [Fintype K] in

theorem diffStep_single_natCast (g : (K → ℤ) → ℤ) (m : K → ℕ) (k : K) :
    diffStep (Pi.single k 1) g (fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ)) =
      g (fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ)) - g (fun j => (m j : ℤ)) := by
  unfold diffStep
  congr 2
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem sum_add_pi_single_one (m : K → ℕ) (k : K) :
    ∑ j, (m + Pi.single k 1 : K → ℕ) j = ∑ j, m j + 1 := by
  simp [Finset.sum_add_distrib]

theorem abs_sub_le_of_unit_steps (G : (K → ℕ) → ℤ) (A : ℕ) (D : ℝ) (hD : 0 ≤ D) (s : ℕ) :
    ∀ a : K → ℕ, ∑ k, a k = s → (∀ k, A ≤ a k) →
      (∀ (m : K → ℕ) (k : K), (∀ j, A ≤ m j) → ∑ j, m j + 1 ≤ s →
        |((G (m + Pi.single k 1) : ℝ) - G m)| ≤ D) →
      |((G a : ℝ) - G (fun _ => A))| ≤ D * s := by
  induction s with
  | zero =>
    intro a hs ha _
    have : a = fun _ => A := by
      funext k
      have h0 := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
      have := ha k
      omega
    subst this
    simp
  | succ s ih =>
    intro a hs ha hstep
    by_cases hall : ∀ k, a k = A
    · have : a = fun _ => A := funext hall
      subst this
      simp only [sub_self, abs_zero]
      positivity
    · push Not at hall
      obtain ⟨k, hk⟩ := hall
      have hk' : A < a k := lt_of_le_of_ne (ha k) (Ne.symm hk)
      set m : K → ℕ := a - Pi.single k 1 with hm_def
      have hma : m + Pi.single k 1 = a := by
        funext j
        by_cases h : j = k
        · subst h; simp [m]; omega
        · simp [m, h]
      have hmA : ∀ j, A ≤ m j := by
        intro j
        by_cases h : j = k
        · subst h; simp [m]; omega
        · simp [m, h]; exact ha j
      have hms : ∑ j, m j = s := by
        have := sum_add_pi_single_one m k
        rw [hma, hs] at this
        omega
      have h1 := ih m hms hmA (fun m' k' hm' hs' => hstep m' k' hm' (by omega))
      have h2 := hstep m k hmA (by omega)
      rw [hma] at h2
      calc |((G a : ℝ) - G (fun _ => A))|
          = |((G a : ℝ) - G m) + ((G m : ℝ) - G (fun _ => A))| := by ring_nf
        _ ≤ |((G a : ℝ) - G m)| + |((G m : ℝ) - G (fun _ => A))| := abs_add_le _ _
        _ ≤ D + D * s := add_le_add h2 h1
        _ = D * ((s + 1 : ℕ) : ℝ) := by push_cast; ring

theorem degLT_succ_growth_natPow (n : ℕ) : ∀ g : (K → ℤ) → ℤ, DegLT g (n + 1) →
    ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, A ≤ a k) →
      |(g (fun k => (a k : ℤ)) : ℝ)| ≤ C * (((∑ k, a k : ℕ) : ℝ) + 1) ^ n := by
  induction n with
  | zero =>
    intro g hg
    have hev : ∀ᶠ m in Filter.atTop, ∀ k, diffStep (Pi.single k 1) g m = 0 := by
      refine Filter.eventually_all.2 fun k => ?_
      have := degLT_diffStep_of_degLT_succ hg (Pi.single k 1) Fin.elim0
      simpa [mixedDiff_of_fin_zero] using this
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hev
    set A : ℕ := ∑ k, (m₀ k).toNat
    have hA : ∀ k, m₀ k ≤ (A : ℤ) := by
      intro k
      calc m₀ k ≤ ((m₀ k).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ (A : ℤ) := by
          exact_mod_cast Finset.single_le_sum (f := fun k => (m₀ k).toNat)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    refine ⟨A, |(g (fun _ => (A : ℤ)) : ℝ)|, abs_nonneg _, fun a ha => ?_⟩
    have hw := abs_sub_le_of_unit_steps (fun a : K → ℕ => g (fun k => (a k : ℤ))) A 0 le_rfl (∑ k, a k) a rfl ha
      (fun m k hm _ => by
        have hge : m₀ ≤ fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ) := by
          intro j
          have := hA j
          have := hm j
          simp only [Pi.add_apply]
          push_cast
          have : (0 : ℤ) ≤ ((Pi.single k 1 : K → ℕ) j : ℤ) := Nat.cast_nonneg _
          omega
        have := hm₀ _ hge k
        rw [diffStep_single_natCast] at this
        rw [sub_eq_zero.mp this]
        simp)
    simp only [zero_mul] at hw
    simp only [pow_zero, mul_one]
    have := abs_sub_abs_le_abs_sub (g (fun k => (a k : ℤ)) : ℝ) (g (fun _ => (A : ℤ)) : ℝ)
    linarith
  | succ n ih =>
    intro g hg
    have hd : ∀ k, ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ j, A ≤ a j) →
        |(diffStep (Pi.single k 1) g (fun j => (a j : ℤ)) : ℝ)| ≤
          C * (((∑ j, a j : ℕ) : ℝ) + 1) ^ n :=
      fun k => ih _ (degLT_diffStep_of_degLT_succ hg _)
    choose Ak Ck hCk hbk using hd
    set A : ℕ := ∑ k, Ak k
    set C : ℝ := ∑ k, Ck k
    have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => hCk k
    have hAk : ∀ k, Ak k ≤ A := fun k =>
      Finset.single_le_sum (f := Ak) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hCk' : ∀ k, Ck k ≤ C := fun k =>
      Finset.single_le_sum (f := Ck) (fun k _ => hCk k) (Finset.mem_univ k)
    set G0 : ℝ := |(g (fun _ => (A : ℤ)) : ℝ)|
    refine ⟨A, G0 + C, by positivity, fun a ha => ?_⟩
    set X : ℝ := ((∑ k, a k : ℕ) : ℝ) + 1 with hX
    have hS0 : (0 : ℝ) ≤ ((∑ k, a k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hX1 : 1 ≤ X := by simp only [X]; linarith
    have hw := abs_sub_le_of_unit_steps (fun a : K → ℕ => g (fun k => (a k : ℤ))) A (C * X ^ n) (by positivity)
      (∑ k, a k) a rfl ha (fun m k hm hs => by
        have h1 := hbk k (m + Pi.single k 1) (fun j => le_trans (hAk k)
          (le_trans (hm j) (by simp)))
        rw [diffStep_single_natCast] at h1
        push_cast at h1 ⊢
        refine le_trans h1 ?_
        have hs' : ((∑ j, (m + Pi.single k 1 : K → ℕ) j : ℕ) : ℝ) + 1 ≤ X := by
          rw [sum_add_pi_single_one]; simp only [X]; exact_mod_cast Nat.add_le_add_right hs 1
        have h0 : (0 : ℝ) ≤ ((∑ j, (m + Pi.single k 1 : K → ℕ) j : ℕ) : ℝ) + 1 := by positivity
        push_cast at hs' h0
        exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hs' n) (hCk k))
          (mul_le_mul_of_nonneg_right (hCk' k) (by positivity)))
    simp only at hw
    have htri := abs_sub_abs_le_abs_sub (g (fun k => (a k : ℤ)) : ℝ) (g (fun _ => (A : ℤ)) : ℝ)
    have hSX : ((∑ k, a k : ℕ) : ℝ) ≤ X := by simp only [X]; linarith
    have hXn : X ^ n * ((∑ k, a k : ℕ) : ℝ) ≤ X ^ (n + 1) := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left hSX (by positivity)
    have hX1n : 1 ≤ X ^ (n + 1) := one_le_pow₀ hX1
    have hG0 : 0 ≤ G0 := abs_nonneg _
    push_cast at hw htri
    calc |(g (fun k => (a k : ℤ)) : ℝ)|
        ≤ G0 + C * X ^ n * ((∑ k, a k : ℕ) : ℝ) := by push_cast; simp only [G0]; linarith
      _ ≤ G0 * X ^ (n + 1) + C * X ^ (n + 1) := by
          have := mul_le_mul_of_nonneg_left hXn hC
          have := mul_le_mul_of_nonneg_left hX1n hG0
          nlinarith
      _ = (G0 + C) * X ^ (n + 1) := by ring

end Growth

theorem DegLTGrowth.proof : DegLTGrowth.Statement := by
  intro K _ _ n g hg
  cases n with
  | zero =>
    have hev : ∀ᶠ m in Filter.atTop, g m = 0 := by
      simpa [mixedDiff_of_fin_zero] using hg Fin.elim0
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hev
    refine ⟨∑ k, (m₀ k).toNat, 0, fun a ha => ?_⟩
    have hge : m₀ ≤ fun k => (a k : ℤ) := by
      intro k
      calc m₀ k ≤ ((m₀ k).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ ((∑ k, (m₀ k).toNat : ℕ) : ℤ) := by
          exact_mod_cast Finset.single_le_sum (f := fun k => (m₀ k).toNat)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        _ ≤ (a k : ℤ) := by exact_mod_cast ha k
    rw [hm₀ _ hge]
    simp
  | succ n =>
    obtain ⟨A, C, _, hb⟩ := degLT_succ_growth_natPow n g hg
    refine ⟨A, C, fun a ha => ?_⟩
    have h := hb a ha
    have he : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
    push_cast at h
    exact h

end GroundTheory.Heights₂.Heights.HilbertSamuel

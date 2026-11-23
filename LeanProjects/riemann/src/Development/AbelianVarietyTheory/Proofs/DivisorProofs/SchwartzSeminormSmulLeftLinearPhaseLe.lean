import Mathlib

open scoped SchwartzMap
open Complex

namespace GlobalTheory.LinPhaseSeminorm

theorem iteratedDeriv_const_mul_cexp (a c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => c * Complex.exp (a * y)) =
      fun y : ℝ => c * a ^ n * Complex.exp (a * y) := by
  induction n generalizing c with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun y : ℝ => c * Complex.exp (a * y)) =
        fun y : ℝ => (c * a) * Complex.exp (a * y) := by
      funext y
      have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
        simpa using (hasDerivAt_id y).ofReal_comp
      have h : HasDerivAt (fun y : ℝ => c * Complex.exp (a * y))
          (c * (Complex.exp (a * y) * (a * 1))) y :=
        ((h1.const_mul a).cexp).const_mul c
      rw [h.deriv]; ring
    rw [hd, ih]; funext y; ring

theorem norm_cexp_neg_two_pi_I_mul (r : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

noncomputable def phaseLine (c t : ℝ) : ℝ → ℂ := fun y =>
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t ^ 2 * c : ℝ) : ℂ)) *
    Complex.exp ((-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ))

theorem phase_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c t : ℝ) :
    (fun x : V => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ)))
      = phaseLine c t ∘ ⇑L := by
  funext x
  simp only [phaseLine, Function.comp_apply, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem contDiff_phaseLine (c t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phaseLine c t) := by
  have ho : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
  unfold phaseLine; fun_prop

theorem norm_iteratedDeriv_phaseLine (c t : ℝ) (i : ℕ) (y : ℝ) :
    ‖iteratedDeriv i (phaseLine c t) y‖ = (2 * Real.pi * |t|) ^ i := by
  have e : phaseLine c t = fun y : ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t ^ 2 * c : ℝ) : ℂ)) *
        Complex.exp ((-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ)) := rfl
  rw [e, iteratedDeriv_const_mul_cexp]
  have h2 : (-(2 * Real.pi * Complex.I) * (t : ℂ)) * (y : ℂ)
      = -(2 * Real.pi * Complex.I) * ((t * y : ℝ) : ℂ) := by push_cast; ring
  simp only
  rw [h2, norm_mul, norm_mul, norm_cexp_neg_two_pi_I_mul, norm_cexp_neg_two_pi_I_mul, norm_pow]
  simp [abs_of_pos Real.pi_pos]

theorem norm_iteratedFDeriv_phase_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c : ℝ) {t : ℝ} (ht : |t| ≤ 1) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ ≤ (2 * Real.pi * ‖L‖) ^ i := by
  rw [L.iteratedFDeriv_comp_right (contDiff_phaseLine c t) x (i := i) (by exact_mod_cast le_top)]
  calc _ ≤ ‖iteratedFDeriv ℝ i (phaseLine c t) (L x)‖ * ∏ _j : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (2 * Real.pi * |t|) ^ i * ‖L‖ ^ i := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_phaseLine]; simp
    _ ≤ (2 * Real.pi * 1) ^ i * ‖L‖ ^ i := by gcongr
    _ = (2 * Real.pi * ‖L‖) ^ i := by ring

theorem hasTemperateGrowth_phase {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c t : ℝ) : Function.HasTemperateGrowth (phaseLine c t ∘ ⇑L) := by
  refine ⟨(contDiff_phaseLine c t).comp L.contDiff, fun n => ⟨0, (2 * Real.pi * |t| * ‖L‖) ^ n, fun x => ?_⟩⟩
  rw [L.iteratedFDeriv_comp_right (contDiff_phaseLine c t) x (i := n) (by exact_mod_cast le_top),
    pow_zero, mul_one]
  calc _ ≤ ‖iteratedFDeriv ℝ n (phaseLine c t) (L x)‖ * ∏ _j : Fin n, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = (2 * Real.pi * |t| * ‖L‖) ^ n := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, norm_iteratedDeriv_phaseLine]; simp [mul_pow]

theorem seminorm_smulLeft_phase_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (c : ℝ) (k n : ℕ), ∃ C : ℝ, ∀ t : ℝ, |t| ≤ 1 → ∀ f : 𝓢(V, ℂ),
      SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ
        (fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * c : ℝ) : ℂ))) f)
        ≤ C * ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m f := by
  intro V _ _ L c k n
  set B : ℝ := 2 ^ n * (1 + 2 * Real.pi * ‖L‖) ^ n with hB
  refine ⟨(n + 1) * B, fun t ht f => ?_⟩
  rw [phase_eq L c t]
  set S := ∑ m ∈ Finset.range (n + 1), SchwartzMap.seminorm ℂ k m f with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun m _ => apply_nonneg _ _
  have hL0 : 0 ≤ 2 * Real.pi * ‖L‖ := by positivity
  have hB0 : 0 ≤ B := by positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have happ : (⇑(SchwartzMap.smulLeftCLM ℂ (phaseLine c t ∘ ⇑L) f))
      = fun y => (phaseLine c t ∘ ⇑L) y * f y := by
    funext y
    rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase L c t), smul_eq_mul]
  rw [happ]
  have hmul := norm_iteratedFDeriv_mul_le (N := ((⊤ : ℕ∞) : WithTop ℕ∞))
    ((contDiff_phaseLine c t).comp L.contDiff) (f.smooth ⊤) x (n := n) (by exact_mod_cast le_top)
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ *
        ‖iteratedFDeriv ℝ (n - i) f x‖) ≤ B * S := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 := norm_iteratedFDeriv_phase_le L c ht i x
    have h2 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖ ≤ S :=
      (SchwartzMap.le_seminorm ℂ k (n - i) f x).trans
        (Finset.single_le_sum (f := fun m => SchwartzMap.seminorm ℂ k m f)
          (fun m _ => apply_nonneg _ _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n i))))
    have hc : (n.choose i : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n i
    have h4 : (2 * Real.pi * ‖L‖) ^ i ≤ (1 + 2 * Real.pi * ‖L‖) ^ n :=
      calc (2 * Real.pi * ‖L‖) ^ i ≤ (1 + 2 * Real.pi * ‖L‖) ^ i := by gcongr; linarith
        _ ≤ (1 + 2 * Real.pi * ‖L‖) ^ n := pow_le_pow_right₀ (by linarith) hi'
    calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ *
          ‖iteratedFDeriv ℝ (n - i) f x‖)
        = ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖) *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f x‖) := by ring
      _ ≤ (2 ^ n * (1 + 2 * Real.pi * ‖L‖) ^ n) * S := by
          gcongr
          exact h1.trans h4
      _ = B * S := by rw [hB]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => (phaseLine c t ∘ ⇑L) y * f y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
        gcongr
    _ = ∑ i ∈ Finset.range (n + 1), ‖x‖ ^ k * ((n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (phaseLine c t ∘ ⇑L) x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (n + 1), B * S := Finset.sum_le_sum hterm
    _ = (n + 1) * B * S := by simp; ring

end GlobalTheory.LinPhaseSeminorm

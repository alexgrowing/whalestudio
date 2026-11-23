import Mathlib

open scoped SchwartzMap ContDiff

namespace GlobalTheory.SchwartzCharMul

theorem iteratedDeriv_cexp_ofReal_mul_I (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) =
      fun t : ℝ => Complex.I ^ n * Complex.exp ((t : ℂ) * Complex.I) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have h : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I) * (1 * Complex.I)) t :=
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp
    rw [(h.const_mul (Complex.I ^ n)).deriv]
    ring

theorem contDiff_cexp_ofReal_mul_I :
    ContDiff ℝ ∞ (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => (Complex.ofRealCLM t : ℂ) * Complex.I) :=
    Complex.ofRealCLM.contDiff.mul contDiff_const
  exact h.cexp

theorem norm_iteratedFDeriv_cexp_ofReal_mul_I (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) t‖ = 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_ofReal_mul_I]
  simp [Complex.norm_exp_ofReal_mul_I]

section Character

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem contDiff_cexp_clm_mul_I (ξ : V →L[ℝ] ℝ) :
    ContDiff ℝ ∞ (fun x : V => Complex.exp ((ξ x : ℂ) * Complex.I)) :=
  contDiff_cexp_ofReal_mul_I.comp ξ.contDiff

theorem norm_iteratedFDeriv_cexp_clm_mul_I_le (ξ : V →L[ℝ] ℝ) (j : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ j (fun x : V => Complex.exp ((ξ x : ℂ) * Complex.I)) x‖ ≤ ‖ξ‖ ^ j := by
  have h : (fun x : V => Complex.exp ((ξ x : ℂ) * Complex.I)) =
      (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) ∘ ξ := rfl
  rw [h, ξ.iteratedFDeriv_comp_right contDiff_cexp_ofReal_mul_I x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp [norm_iteratedFDeriv_cexp_ofReal_mul_I]

theorem norm_pow_mul_iteratedFDeriv_cexp_clm_mul_le (g : 𝓢(V, ℂ)) (ξ : V →L[ℝ] ℝ)
    (k n : ℕ) (x : V) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : V => Complex.exp ((ξ x : ℂ) * Complex.I) * g x) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) g) *
        (1 + ‖ξ‖) ^ n := by
  have hL := norm_iteratedFDeriv_mul_le (contDiff_cexp_clm_mul_I ξ) (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x : V => Complex.exp ((ξ x : ℂ) * Complex.I) * g x) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((ξ x : ℂ) * Complex.I)) x‖ *
          ‖iteratedFDeriv ℝ (n - i) g x‖ :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun x : V => Complex.exp ((ξ x : ℂ) * Complex.I)) x‖ *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n - i) g x‖) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (1 + ‖ξ‖) ^ n *
          SchwartzMap.seminorm ℂ k (n - i) g := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 := norm_iteratedFDeriv_cexp_clm_mul_I_le ξ i x
        have h2 : ‖ξ‖ ^ i ≤ (1 + ‖ξ‖) ^ n :=
          (pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg ξ]) i).trans
            (pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) hi')
        have h3 := SchwartzMap.le_seminorm ℂ k (n - i) g x
        gcongr
        · exact h1.trans h2
    _ = _ := by rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring

noncomputable def charMul (g : 𝓢(V, ℂ)) (ξ : V →L[ℝ] ℝ) : 𝓢(V, ℂ) where
  toFun x := Complex.exp ((ξ x : ℂ) * Complex.I) * g x
  smooth' := (contDiff_cexp_clm_mul_I ξ).mul (g.smooth ⊤)
  decay' k n := ⟨_, norm_pow_mul_iteratedFDeriv_cexp_clm_mul_le g ξ k n⟩

theorem exists_charMul_schwartz_bound :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (g : SchwartzMap V ℂ),
    ∃ H : (V →L[ℝ] ℝ) → SchwartzMap V ℂ, (∀ ξ x, H ξ x = Complex.exp ((ξ x : ℂ) * Complex.I) * g x) ∧
      ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (H ξ) x‖ ≤ C * (1 + ‖ξ‖) ^ n := by
  intro V _ _ _ g
  refine ⟨charMul g, fun ξ x => rfl, fun k n =>
    ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * SchwartzMap.seminorm ℂ k (n - i) g,
      fun ξ x => ?_⟩⟩
  exact norm_pow_mul_iteratedFDeriv_cexp_clm_mul_le g ξ k n x

end Character

end GlobalTheory.SchwartzCharMul

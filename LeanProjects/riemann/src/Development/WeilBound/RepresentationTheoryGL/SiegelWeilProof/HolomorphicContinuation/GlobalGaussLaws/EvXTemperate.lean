import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzGaussWidth
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocOpSt

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

theorem evX_temperate {m n : ℕ} (P : PX m n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => evX P u) := by
  have hcoord : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => u a i) := by
    intro a i
    exact ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ))).hasTemperateGrowth
  have hconj : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u a i)) := by
    intro a i
    have h := (Complex.conjCLE.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
    convert h using 1
    funext u
    simp [Complex.conjCLE_apply]
  refine MvPolynomial.induction_on
    (motive := fun Q : PX m n =>
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => evX Q u)) P ?_ ?_ ?_
  · intro a
    convert Function.HasTemperateGrowth.const (E := Fin m → Fin n → ℂ) a using 1
    funext u
    simp [evX]
  · intro p q hp hq
    convert hp.add hq using 1
    funext u
    simp [evX]
  · intro p k hp
    obtain ⟨a, i, b⟩ := k
    cases b
    · have e : (fun u : Fin m → Fin n → ℂ => evX (p * X (a, i, false)) u) =
          (fun u => evX p u) * (fun u => u a i) := by
        funext u
        simp [evX]
      rw [e]
      exact hp.mul (hcoord a i)
    · have e : (fun u : Fin m → Fin n → ℂ => evX (p * X (a, i, true)) u) =
          (fun u => evX p u) * (fun u => star (u a i)) := by
        funext u
        simp [evX]
      rw [e]
      exact hp.mul (hconj a i)

private theorem hasTemperateGrowth_const_mul_sum_norm_sq {m n : ℕ} (c : ℝ) :
    Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
  have hre : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => (u a i).re) := fun a i =>
    (Complex.reCLM.comp ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
  have him : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => (u a i).im) := fun a i =>
    (Complex.imCLM.comp ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
  have hsq : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => ‖u a i‖ ^ 2) := by
    intro a i
    have e : (fun u : Fin m → Fin n → ℂ => ‖u a i‖ ^ 2) =
        fun u : Fin m → Fin n → ℂ => (u a i).re * (u a i).re + (u a i).im * (u a i).im := by
      funext u
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [e]
    exact ((hre a i).mul (hre a i)).add ((him a i).mul (him a i))
  have hin : ∀ a : Fin m, Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => ∑ i : Fin n, ‖u a i‖ ^ 2) := fun a =>
    Function.HasTemperateGrowth.sum fun i _ => hsq a i
  have hsum : Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) :=
    Function.HasTemperateGrowth.sum fun a _ => hin a
  exact (Function.HasTemperateGrowth.const c).mul hsum

private theorem norm_iteratedFDeriv_cexp_neg_eq_exp_neg (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (fun s : ℝ => Complex.exp (-(s : ℂ))) t‖ = Real.exp (-t) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hit : iteratedDeriv i (fun s : ℝ => Complex.exp (-(s : ℂ))) =
      fun s : ℝ => (-1 : ℂ) ^ i * Complex.exp (-(s : ℂ)) := by
    induction i with
    | zero =>
      funext s
      simp
    | succ i ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
        simpa using (hasDerivAt_id s).ofReal_comp
      have hd : HasDerivAt (fun s : ℝ => -(s : ℂ)) (-1) s := h0.neg
      have he := (hd.cexp).const_mul ((-1 : ℂ) ^ i)
      rw [he.deriv]
      ring
  rw [hit]
  simp [Complex.norm_exp]

private theorem exists_bound_one_add_pow_mul_exp_neg_sq (c : ℝ) (hc : 0 < c) (j : ℕ) :
    ∃ M : ℝ, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ j * Real.exp (-(c * r ^ 2)) ≤ M := by
  refine ⟨2 ^ j * (1 + j.factorial / c ^ j), fun r hr => ?_⟩
  have hy : 0 ≤ c * r ^ 2 := by positivity
  have hexp := Real.pow_div_factorial_le_exp (c * r ^ 2) hy j
  have hE : 0 < Real.exp (c * r ^ 2) := Real.exp_pos _
  have hcj : 0 < c ^ j := pow_pos hc j
  have h2j : (0 : ℝ) < 2 ^ j := pow_pos two_pos j
  have hr2j : 0 ≤ (r ^ 2) ^ j := by positivity
  have h1 : (1 + r) ^ j ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by
    rcases le_total r 1 with h | h
    · calc (1 + r) ^ j ≤ 2 ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
        _ ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by nlinarith
    · calc (1 + r) ^ j ≤ (2 * r ^ 2) ^ j := pow_le_pow_left₀ (by linarith) (by nlinarith) j
        _ = 2 ^ j * (r ^ 2) ^ j := mul_pow _ _ _
        _ ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by nlinarith
  have h2 : (r ^ 2) ^ j * Real.exp (-(c * r ^ 2)) ≤ j.factorial / c ^ j := by
    rw [mul_pow, div_le_iff₀ (by positivity)] at hexp
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE hcj]
    nlinarith
  have h3 : Real.exp (-(c * r ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  calc (1 + r) ^ j * Real.exp (-(c * r ^ 2))
      ≤ 2 ^ j * (1 + (r ^ 2) ^ j) * Real.exp (-(c * r ^ 2)) := by gcongr
    _ = 2 ^ j * (Real.exp (-(c * r ^ 2)) + (r ^ 2) ^ j * Real.exp (-(c * r ^ 2))) := by ring
    _ ≤ 2 ^ j * (1 + j.factorial / c ^ j) :=
        mul_le_mul_of_nonneg_left (add_le_add h3 h2) h2j.le

theorem gs_sch {m n : ℕ} (c : ℝ) (hc : 0 < c) :
    ∃ S : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, S u = gs c u := by
  have hqT := hasTemperateGrowth_const_mul_sum_norm_sq (m := m) (n := n) c
  have hhC : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Complex.exp (-(s : ℂ))) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.neg)
  have hgs : (gs c : (Fin m → Fin n → ℂ) → ℂ) =
      (fun s : ℝ => Complex.exp (-(s : ℂ))) ∘
        (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
    funext u
    simp [gs]
  have hlow : ∀ u : Fin m → Fin n → ℂ, ‖u‖ ^ 2 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 := by
    intro u
    have hS0 : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 := by positivity
    have hb : ‖u‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      have h1 : ‖u a i‖ ^ 2 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 :=
        calc ‖u a i‖ ^ 2 ≤ ∑ i' : Fin n, ‖u a i'‖ ^ 2 :=
              Finset.single_le_sum (f := fun i' => ‖u a i'‖ ^ 2)
                (fun _ _ => by positivity) (Finset.mem_univ i)
          _ ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 :=
              Finset.single_le_sum (f := fun a' => ∑ i' : Fin n, ‖u a' i'‖ ^ 2)
                (fun _ _ => by positivity) (Finset.mem_univ a)
      have h2 := Real.abs_le_sqrt h1
      rwa [abs_of_nonneg (norm_nonneg _)] at h2
    calc ‖u‖ ^ 2 ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = _ := Real.sq_sqrt hS0
  refine ⟨⟨gs c, ?_, ?_⟩, fun u => rfl⟩
  · rw [hgs]
    exact hhC.comp hqT.1
  · intro k N
    obtain ⟨K, C, hC0, hC⟩ := hqT.norm_iteratedFDeriv_le_uniform N
    obtain ⟨M, hM⟩ := exists_bound_one_add_pow_mul_exp_neg_sq c hc (k + K * N)
    refine ⟨N.factorial * (C + 1) ^ N * M, fun u => ?_⟩
    have hu0 := norm_nonneg u
    have hD1 : 1 ≤ (C + 1) * (1 + ‖u‖) ^ K :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
    have hD : ∀ i : ℕ, 1 ≤ i → i ≤ N →
        ‖iteratedFDeriv ℝ i
          (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) u‖ ≤
          ((C + 1) * (1 + ‖u‖) ^ K) ^ i := by
      intro i hi1 hiN
      calc _ ≤ C * (1 + ‖u‖) ^ K := hC i hiN u
        _ ≤ (C + 1) * (1 + ‖u‖) ^ K := by gcongr; linarith
        _ ≤ _ := le_self_pow₀ hD1 (by omega)
    have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := N) hhC hqT.1
      (by exact_mod_cast le_top) u
      (C := Real.exp (-(c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)))
      (fun i _ => (norm_iteratedFDeriv_cexp_neg_eq_exp_neg i _).le) hD
    have hexp_le : Real.exp (-(c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)) ≤
        Real.exp (-(c * ‖u‖ ^ 2)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left (hlow u) hc.le
      linarith
    have hpow : ‖u‖ ^ k ≤ (1 + ‖u‖) ^ k := pow_le_pow_left₀ hu0 (by linarith) k
    rw [hgs]
    calc ‖u‖ ^ k * ‖iteratedFDeriv ℝ N _ u‖
        ≤ (1 + ‖u‖) ^ k * (N.factorial * Real.exp (-(c * ‖u‖ ^ 2)) *
            ((C + 1) * (1 + ‖u‖) ^ K) ^ N) := by
          refine mul_le_mul hpow (key.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = N.factorial * (C + 1) ^ N *
            ((1 + ‖u‖) ^ (k + K * N) * Real.exp (-(c * ‖u‖ ^ 2))) := by
          rw [mul_pow, ← pow_mul, pow_add]
          ring
      _ ≤ N.factorial * (C + 1) ^ N * M := by
          gcongr
          exact hM _ hu0

theorem schFP : SchFP := by
  intro m n c hc P
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => evX P u) S, ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evX_temperate P)]
  funext u
  simp [fP, hS, smul_eq_mul]

end PositivityTheory.Rg.Sw.Glob

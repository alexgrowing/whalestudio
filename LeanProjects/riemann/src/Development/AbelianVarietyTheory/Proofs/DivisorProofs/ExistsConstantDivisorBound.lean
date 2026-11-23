import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.DegreeFormula.PointDegree.PowSum
import Development.AbelianVarietyTheory.Definitions.Foundations.AltCoeffRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaHookBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLogDivSqPrimesTail

open MvPolynomial Finset GlobalTheory.FlagHook Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.WeightThresholdDefs

namespace GlobalTheory.TailBound

theorem tsum_abs_le (x m : ℝ) (hx : 0 ≤ x) (hx2 : x ≤ 1 / 2) (hm : 0 ≤ m) (F : ℕ → ℝ)
    (hF : ∀ n, |F n| ≤ x ^ (n + 1) * m) : ∑' n, |F n| ≤ 2 * x * m := by
  have h1 : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * (x * m)) (2 * (x * m)) :=
    hasSum_geometric_two.mul_right _
  have h2 : ∀ n, ‖|F n|‖ ≤ (1 / 2 : ℝ) ^ n * (x * m) := by
    intro n
    rw [Real.norm_eq_abs, abs_abs]
    refine (hF n).trans ?_
    have : x ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ hx hx2 n
    calc x ^ (n + 1) * m = x ^ n * (x * m) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this (mul_nonneg hx hm)
  have h3 := tsum_of_norm_bounded h1 h2
  calc ∑' n, |F n| ≤ ‖∑' n, |F n|‖ := Real.le_norm_self _
    _ ≤ 2 * (x * m) := h3
    _ = _ := by ring

theorem sum_tsum_abs_le (p b c : ℝ) (hp : 2 ≤ p) (hb : 0 ≤ b) (hbp : b ≤ p / 2) (hc : 0 ≤ c) (N : ℕ)
    (F : ℕ → ℕ → ℝ)
    (hF : ∀ k ∈ Icc 2 N, ∀ n, |F k n| ≤ (p ^ k)⁻¹ ^ (n + 1) * (c * b ^ (k - 1))) :
    ∑ k ∈ Icc 2 N, ∑' n, |F k n| ≤ 4 * c * b / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  have h1 : ∀ k ∈ Icc 2 N, ∑' n, |F k n| ≤ (2 * c * b / p ^ 2) * (1 / 2 : ℝ) ^ (k - 2) := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by have := (mem_Icc.1 hk).1; omega⟩
    have hx : (p ^ (m + 2))⁻¹ ≤ 1 / 2 := by
      rw [one_div]
      refine inv_anti₀ (by norm_num) (hp.trans ?_)
      exact le_self_pow₀ (by linarith) (by omega)
    refine (tsum_abs_le _ _ (by positivity) hx (by positivity) _ (hF _ hk)).trans ?_
    have h2 : (b / p) ^ m ≤ (1 / 2 : ℝ) ^ m := by
      refine pow_le_pow_left₀ (by positivity) ?_ m
      rw [div_le_iff₀ hp0]; linarith
    have e1 : m + 2 - 1 = m + 1 := by omega
    have e2 : m + 2 - 2 = m := by omega
    rw [e1, e2]
    calc 2 * (p ^ (m + 2))⁻¹ * (c * b ^ (m + 1)) = (2 * c * b / p ^ 2) * (b / p) ^ m := by
          rw [div_pow]; field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  refine (sum_le_sum h1).trans ?_
  rw [← mul_sum]
  have h3 : ∑ k ∈ Icc 2 N, (1 / 2 : ℝ) ^ (k - 2) ≤ 2 := by
    have : ∑ k ∈ Icc 2 N, (1 / 2 : ℝ) ^ (k - 2) = ∑ m ∈ range (N + 1 - 2), (1 / 2 : ℝ) ^ m := by
      rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
      simp
    rw [this]
    exact sum_geometric_two_le _
  calc _ ≤ (2 * c * b / p ^ 2) * 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

section Kap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem kap_sum (u : ι → Fin N → ℝ) (k : ℕ) (S : Finset (Fin N))
    (γ : Fin N → MvPolynomial (ι × Fin N) ℝ) (Q : MvPolynomial (ι × Fin N) ℝ) :
    kap u k (∑ i ∈ S, γ i) Q = ∑ i ∈ S, kap u k (γ i) Q := by
  unfold kap
  rw [sum_mul, PPowSum.degFl_sum, mul_sum, sum_div]

theorem kap_C_mul (u : ι → Fin N → ℝ) (k : ℕ) (c : ℝ) (γ Q : MvPolynomial (ι × Fin N) ℝ) :
    kap u k (C c * γ) Q = c * kap u k γ Q := by
  unfold kap
  rw [mul_assoc, PPowSum.degFl_C_mul]; ring

theorem kap_compl (u : ι → Fin N → ℝ) (k m : ℕ) (hm : 1 ≤ m) (τ' : ι) (S : Finset (Fin N))
    (Q : MvPolynomial (ι × Fin N) ℝ) :
    kap u k (∑ i ∈ Sᶜ, X (τ', i) ^ m) Q = - kap u k (∑ i ∈ S, X (τ', i) ^ m) Q := by
  have h0 : kap u k (∑ i, X (τ', i) ^ m) Q = 0 := by
    unfold kap
    rw [degreePowerSumMulEqZero ι N τ' m Q hm]; simp
  rw [kap_sum, ← sum_add_sum_compl S] at h0
  rw [kap_sum, kap_sum]; linarith

theorem abs_kap_block_le (u : ι → Fin N → ℝ) (k m : ℕ) (hm : 1 ≤ m) (τ' : ι) (S T : Finset (Fin N))
    (hT : T = S ∨ T = Sᶜ) (Q : MvPolynomial (ι × Fin N) ℝ) (M : ℝ)
    (hM : ∀ i ∈ S, |kap u k (X (τ', i) ^ m) Q| ≤ M) :
    |kap u k (∑ i ∈ T, X (τ', i) ^ m) Q| ≤ S.card * M := by
  have h : |kap u k (∑ i ∈ S, X (τ', i) ^ m) Q| ≤ S.card * M := by
    rw [kap_sum]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    simpa using sum_le_card_nsmul S _ M hM
  rcases hT with rfl | rfl
  · exact h
  · rw [kap_compl u k m hm, abs_neg]; exact h

end Kap

open Classical

section Shim
variable {D : D7} (Y : ShimX D.what₂.Tau)

theorem card_small : (univ.filter (fun i : Fin Y.N => inSmall Y i)).card = jS Y := by
  have hj := Y.j_lt
  have h1 : (univ.filter (fun i : Fin Y.N => (i : ℕ) < Y.j)).card = Y.j := by
    rw [Fin.card_filter_val_lt]; omega
  unfold jS
  by_cases h : Y.j ≤ Y.N - Y.j
  · have : univ.filter (fun i : Fin Y.N => inSmall Y i) = univ.filter (fun i : Fin Y.N => (i : ℕ) < Y.j) := by
      ext i; simp [inSmall, h]
    rw [this, h1]; omega
  · have : univ.filter (fun i : Fin Y.N => inSmall Y i) = (univ.filter (fun i : Fin Y.N => (i : ℕ) < Y.j))ᶜ := by
      ext i; simp [inSmall, h]
    rw [this, card_compl, h1, Fintype.card_fin]; omega

theorem abs_kap_chLie_le (u : D.what₂.Tau → Fin Y.N → ℝ) (k m : ℕ) (hm : 1 ≤ m) (σ : EmbC D)
    (Q : MvPolynomial (D.what₂.Tau × Fin Y.N) ℝ) (M : ℝ)
    (hM : ∀ τ' i, inSmall Y i → |kap u k (X (τ', i) ^ m) Q| ≤ M) :
    (m.factorial : ℝ) * |kap u k (chLie Y.j m σ) Q| ≤ jS Y * M := by
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have key : ∀ (τ' : D.what₂.Tau) (T : Finset (Fin Y.N)),
      (T = univ.filter (fun i : Fin Y.N => inSmall Y i) ∨
        T = (univ.filter (fun i : Fin Y.N => inSmall Y i))ᶜ) →
      |kap u k (∑ i ∈ T, X (τ', i) ^ m) Q| ≤ jS Y * M := by
    intro τ' T hT
    have := abs_kap_block_le u k m hm τ' _ T hT Q M (fun i hi => hM τ' i (mem_filter.1 hi).2)
    rwa [card_small] at this
  rcases σ with τ' | τ'
  · have e : chLie Y.j m (Sum.inl τ' : EmbC D) = C ((m.factorial : ℝ)⁻¹) *
        ∑ i ∈ univ.filter (fun i : Fin Y.N => (i : ℕ) < Y.j), X (τ', i) ^ m := rfl
    rw [e, kap_C_mul, abs_mul, abs_of_pos (inv_pos.2 hf), ← mul_assoc, mul_inv_cancel₀ hf.ne', one_mul]
    apply key
    by_cases h : Y.j ≤ Y.N - Y.j
    · left; ext i; simp [inSmall, h]
    · right; ext i; simp [inSmall, h]
  · have e : chLie Y.j m (Sum.inr τ' : EmbC D) = C ((m.factorial : ℝ)⁻¹) * (C ((-1 : ℝ) ^ m) *
        ∑ i ∈ univ.filter (fun i : Fin Y.N => Y.j ≤ (i : ℕ)), X (τ', i) ^ m) := by
      change C ((m.factorial : ℝ)⁻¹) *
        ∑ i ∈ univ.filter (fun i : Fin Y.N => Y.j ≤ (i : ℕ)), (-X (τ', i)) ^ m = _
      congr 1
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [neg_pow]; simp
    rw [e, kap_C_mul, kap_C_mul, abs_mul, abs_of_pos (inv_pos.2 hf), ← mul_assoc,
      mul_inv_cancel₀ hf.ne', one_mul, abs_mul, abs_neg_one_pow, one_mul]
    apply key
    by_cases h : Y.j ≤ Y.N - Y.j
    · right; ext i; simp [inSmall, h]
    · left; ext i; simp [inSmall, h]

theorem abs_term_le (hc : ∀ Q, Y.chern Q = Y.vol * degFl D.what₂.Tau Y.N Q)
    (u : D.what₂.Tau → Fin Y.N → ℝ) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 ≤ t)
    (γ Q : MvPolynomial (D.what₂.Tau × Fin Y.N) ℝ) :
    |(k.factorial : ℝ) * t * Y.chern (γ * Q) / (((dimY Y : ℝ) + 1) * geoDeg Y u)| ≤
      t * (((k - 1).factorial : ℝ) * |kap u k γ Q|) := by
  unfold geoDeg
  rw [hc, hc]
  by_cases hv : Y.vol = 0
  · rw [hv]; simp only [zero_mul, mul_zero, div_zero, abs_zero]; positivity
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have e : ((m + 1).factorial : ℝ) * t * (Y.vol * degFl D.what₂.Tau Y.N (γ * Q)) /
        (((dimY Y : ℝ) + 1) * (Y.vol * degFl D.what₂.Tau Y.N (linRoot u ^ dimY Y))) =
        t * ((m.factorial : ℝ) * kap u (m + 1) γ Q) := by
      unfold kap flagDeg
      rw [show ((m + 1).factorial : ℝ) * t * (Y.vol * degFl D.what₂.Tau Y.N (γ * Q)) =
          Y.vol * (t * ((m.factorial : ℝ) * (((m + 1 : ℕ) : ℝ) * degFl D.what₂.Tau Y.N (γ * Q)))) by
        rw [Nat.factorial_succ]; push_cast; ring,
        mul_left_comm _ Y.vol, mul_div_mul_left _ _ hv, mul_div_assoc, mul_div_assoc]
    rw [e, Nat.add_sub_cancel, abs_mul, abs_mul, abs_of_nonneg ht, Nat.abs_cast]

theorem abs_le_supAbs (u : D.what₂.Tau → Fin Y.N → ℝ) (τ : D.what₂.Tau) (i : Fin Y.N) :
    |u τ i| ≤ supAbs Y u :=
  le_ciSup (f := fun x : Rt D.what₂.Tau Y.N => |u x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)

theorem spread_spec (u : D.what₂.Tau → Fin Y.N → ℝ) (τ : D.what₂.Tau) :
    (∀ a b, u τ a - u τ b ≤ (⨆ i, u τ i) - ⨅ i, u τ i) ∧ 0 ≤ (⨆ i, u τ i) - (⨅ i, u τ i) ∧
      (⨆ i, u τ i) - (⨅ i, u τ i) ≤ 2 * supAbs Y u := by
  haveI : Nonempty (Fin Y.N) := ⟨⟨Y.j, Y.j_lt⟩⟩
  have h : ∀ a b, u τ a - u τ b ≤ (⨆ i, u τ i) - ⨅ i, u τ i := fun a b =>
    sub_le_sub (le_ciSup (Set.finite_range _).bddAbove a) (ciInf_le (Set.finite_range _).bddBelow b)
  refine ⟨h, by simpa using h ⟨Y.j, Y.j_lt⟩ ⟨Y.j, Y.j_lt⟩, ?_⟩
  have h1 : (⨆ i, u τ i) ≤ supAbs Y u := ciSup_le fun i => (abs_le.1 (abs_le_supAbs Y u τ i)).2
  have h2 : -supAbs Y u ≤ ⨅ i, u τ i := le_ciInf fun i => (abs_le.1 (abs_le_supAbs Y u τ i)).1
  linarith

theorem big_b0_lower_bound (u : D.what₂.Tau → Fin Y.N → ℝ) (g : ℝ) (hg : 0 < g) :
    0 ≤ supAbs Y u / g ∧ 8 * (Y.N : ℝ) * (1 + supAbs Y u / g) ≤ bigB0 Y u g := by
  have h0 : 0 ≤ supAbs Y u := Real.iSup_nonneg fun _ => abs_nonneg _
  have hH : 0 ≤ supAbs Y u / g := div_nonneg h0 hg.le
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  have hN : (2 : ℝ) ≤ Y.N := by
    have h1 := Y.j_pos
    have h2 := Y.j_lt
    exact_mod_cast (by omega : 2 ≤ Y.N)
  refine ⟨hH, ?_⟩
  unfold bigB0
  refine mul_le_mul_of_nonneg_right ?_ (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hf (sq_nonneg (Y.N : ℝ))]

end Shim

end GlobalTheory.TailBound

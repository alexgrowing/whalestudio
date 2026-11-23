import Mathlib

open scoped ContDiff

noncomputable section

namespace PI.UnitaryGroupMassFormula.UsCost.ZI

section quad

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem norm_iteratedFDeriv_le_of_fderiv_eq_quadratic
    (Bi : W →L[ℝ] W →L[ℝ] (V →L[ℝ] W)) {U : Set V} (hU : IsOpen U) {φ : V → W}
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n φ U) (hd : ∀ z ∈ U, fderiv ℝ φ z = Bi (φ z) (φ z)) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ U, ‖iteratedFDeriv ℝ a φ z‖ ≤ K * max 1 ‖φ z‖ ^ (a + 1) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  rcases a with _ | a
  · refine ⟨1, zero_le_one, fun z _ => ?_⟩
    rw [norm_iteratedFDeriv_zero, one_mul, zero_add, pow_one]
    exact le_max_right _ _
  · choose! K hK0 hK using ih
    refine ⟨‖Bi‖ * ∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * (K i * K (a - i)),
      mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i hi => ?_), fun z hz => ?_⟩
    · have hi' := Finset.mem_range.1 hi
      exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hK0 i (by omega)) (hK0 (a - i) (by omega)))
    · have hm : 1 ≤ max 1 ‖φ z‖ := le_max_left _ _
      have hm0 : 0 ≤ max 1 ‖φ z‖ := zero_le_one.trans hm
      have heq : Set.EqOn (fderiv ℝ φ) (fun y => Bi (φ y) (φ y)) U := fun y hy => hd y hy
      have e1 : ‖iteratedFDeriv ℝ (a + 1) φ z‖ =
          ‖iteratedFDerivWithin ℝ a (fun y => Bi (φ y) (φ y)) U z‖ := by
        rw [← norm_iteratedFDeriv_fderiv,
          ← (iteratedFDerivWithin_of_isOpen a hU hz :
            iteratedFDerivWithin ℝ a (fderiv ℝ φ) U z = iteratedFDeriv ℝ a (fderiv ℝ φ) z),
          iteratedFDerivWithin_congr heq hz]
      rw [e1]
      refine (Bi.norm_iteratedFDerivWithin_le_of_bilinear (hφ a) (hφ a) hU.uniqueDiffOn hz
        le_rfl).trans ?_
      rw [mul_assoc ‖Bi‖, Finset.sum_mul]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (norm_nonneg _)
      have hi' := Finset.mem_range.1 hi
      rw [iteratedFDerivWithin_of_isOpen i hU hz, iteratedFDerivWithin_of_isOpen (a - i) hU hz]
      have h1 := hK i (by omega) z hz
      have h2 := hK (a - i) (by omega) z hz
      have hpow : max 1 ‖φ z‖ ^ (a + 1 + 1) =
          max 1 ‖φ z‖ ^ (i + 1) * max 1 ‖φ z‖ ^ (a - i + 1) := by
        rw [← pow_add]; congr 1; omega
      calc (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ z‖ * ‖iteratedFDeriv ℝ (a - i) φ z‖
          ≤ (a.choose i : ℝ) * (K i * max 1 ‖φ z‖ ^ (i + 1)) *
              (K (a - i) * max 1 ‖φ z‖ ^ (a - i + 1)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
            exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hK0 i (by omega)) (pow_nonneg hm0 _))
        _ = (a.choose i : ℝ) * (K i * K (a - i)) * max 1 ‖φ z‖ ^ (a + 1 + 1) := by
            rw [hpow]; ring

theorem quad_bound (Bi : W →L[ℝ] W →L[ℝ] (V →L[ℝ] W)) {U : Set V} (hU : IsOpen U) {φ : V → W}
    (hφ : ∀ n : ℕ, ContDiffOn ℝ n φ U) (hd : ∀ z ∈ U, fderiv ℝ φ z = Bi (φ z) (φ z)) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ U, ∀ a ≤ n, ‖iteratedFDeriv ℝ a φ z‖ ≤ K * max 1 ‖φ z‖ ^ (a + 1) := by
  choose K hK0 hK using norm_iteratedFDeriv_le_of_fderiv_eq_quadratic Bi hU hφ hd
  refine ⟨∑ a ∈ Finset.range (n + 1), K a, Finset.sum_nonneg fun a _ => hK0 a,
    fun z hz a ha => ?_⟩
  refine (hK a z hz).trans (mul_le_mul_of_nonneg_right ?_
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  exact Finset.single_le_sum (f := K) (fun b _ => hK0 b) (Finset.mem_range.2 (by omega))

end quad

section words

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype I]

theorem norm_smulRightL_le (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ‖ContinuousLinearMap.smulRightL ℝ V E‖ ≤ 1 := by
  exact ContinuousLinearMap.norm_smulRightL_le

private theorem one_le_pow_of_one_le_real {x : ℝ} (hx : 1 ≤ x) (n : ℕ) : 1 ≤ x ^ n := by
  exact one_le_pow₀ hx

private theorem pow_le_pow_right_of_one_le {x : ℝ} (hx : 1 ≤ x) {m n : ℕ} (h : m ≤ n) :
    x ^ m ≤ x ^ n := by
  exact pow_le_pow_right₀ hx h

private theorem mul_pow_mul_le_mul_pow_succ {Kc R β lam M : ℝ} {b j : ℕ} (hj : j ≤ b) (hKc : 0 ≤ Kc)
    (hR : 1 ≤ R) (hβ : 0 ≤ β) (hlam : 1 ≤ lam) (hM : 1 ≤ M) :
    Kc * M ^ (j + 1) * (R ^ (b - j) * (β * lam) * (lam * M) ^ (b - j)) ≤
      Kc * R ^ b * β * (lam * M) ^ (b + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left]
  have hM0 : 0 ≤ M := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hlam0 : 0 ≤ lam := by linarith
  have hL : 0 ≤ Kc * M ^ (j + 1) * (R ^ k * (β * lam) * (lam * M) ^ k) :=
    mul_nonneg (mul_nonneg hKc (pow_nonneg hM0 _))
      (mul_nonneg (mul_nonneg (pow_nonneg hR0 _) (mul_nonneg hβ hlam0))
        (pow_nonneg (mul_nonneg hlam0 hM0) _))
  have hX : 1 ≤ R ^ j * lam ^ j :=
    one_le_mul_of_one_le_of_one_le (one_le_pow_of_one_le_real hR j)
      (one_le_pow_of_one_le_real hlam j)
  calc _ ≤ Kc * M ^ (j + 1) * (R ^ k * (β * lam) * (lam * M) ^ k) * (R ^ j * lam ^ j) :=
        le_mul_of_one_le_right hL hX
    _ = _ := by ring

theorem iter_words (q : ℕ) (Kc : ℝ) (hKc : 0 ≤ Kc) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {α E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Cls : ℕ → (α → E) → Prop)
      (Dop : I → (α → E) → (α → E)) (Γ : V → α) (U : Set V) (c : I → V → (V →L[ℝ] ℝ)) (z₀ : V)
      (M lam : ℝ),
      IsOpen U → z₀ ∈ U → 1 ≤ M → 1 ≤ lam →
      (∀ b H, Cls (b + 1) H → Cls b H) →
      (∀ b H i, Cls (b + 1) H → Cls b (Dop i H)) →
      (∀ b H, Cls b H → ∀ z ∈ U, ContDiffAt ℝ b (fun z => H (Γ z)) z) →
      (∀ b H, Cls (b + 1) H → ∀ z ∈ U,
        fderiv ℝ (fun z => H (Γ z)) z = ∑ i, (c i z).smulRight (Dop i H (Γ z))) →
      (∀ i (n : ℕ), ContDiffOn ℝ n (c i) U) →
      (∀ i, ∀ a ≤ q, ‖iteratedFDeriv ℝ a (c i) z₀‖ ≤ Kc * M ^ (a + 1)) →
      ∀ b ≤ q, ∀ (H : α → E) (β : ℝ), Cls b H →
        (∀ w : List I, w.length ≤ b → ‖w.foldr Dop H (Γ z₀)‖ ≤ β * lam ^ w.length) →
        ‖iteratedFDeriv ℝ b (fun z => H (Γ z)) z₀‖ ≤ C * β * (lam * M) ^ b := by
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ((Fintype.card I : ℝ) * Kc + 1) * 2 ^ q := ⟨_, rfl⟩
  have hNK : 0 ≤ (Fintype.card I : ℝ) * Kc := mul_nonneg (Nat.cast_nonneg _) hKc
  have hR : 1 ≤ R := by
    rw [hRdef]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow_of_one_le_real (by norm_num) q)
  have hR0 : 0 ≤ R := by linarith
  refine ⟨R ^ q, one_le_pow_of_one_le_real hR q, ?_⟩
  intro α E _ _ Cls Dop Γ U c z₀ M lam hU hz₀ hM hlam hdown hDop hsmooth hderiv hc hcb
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  have hmono : ∀ a b (H : α → E), a ≤ b → Cls b H → Cls a H := by
    intro a b H hab
    induction hab with
    | refl => exact id
    | step _ ih => exact fun h => ih (hdown _ _ h)
  have key : ∀ b, b ≤ q → ∀ (H : α → E) (β : ℝ), Cls b H →
      (∀ w : List I, w.length ≤ b → ‖w.foldr Dop H (Γ z₀)‖ ≤ β * lam ^ w.length) →
      ‖iteratedFDeriv ℝ b (fun z => H (Γ z)) z₀‖ ≤ R ^ b * β * (lam * M) ^ b := by
    intro b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
    intro hb H β hH hw
    have hβ0 : ‖H (Γ z₀)‖ ≤ β := by simpa using hw [] (Nat.zero_le _)
    have hβ : 0 ≤ β := (norm_nonneg _).trans hβ0
    rcases b with _ | b
    · simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, mul_one]
      exact hβ0
    · obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Kc * R ^ b * β * (lam * M) ^ (b + 1) := ⟨_, rfl⟩
      have hG : ∀ i, ContDiffOn ℝ b (fun z => Dop i H (Γ z)) U := fun i z hz =>
        (hsmooth b (Dop i H) (hDop b H i hH) z hz).contDiffWithinAt
      have hf : ∀ i, ContDiffOn ℝ b
          (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U := fun i =>
        ((ContinuousLinearMap.smulRightL ℝ V E).contDiff.comp_contDiffOn (hc i b)).clm_apply (hG i)
      have heq : Set.EqOn (fderiv ℝ (fun z => H (Γ z)))
          (∑ i, fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U := by
        intro z hz
        rw [Finset.sum_apply, hderiv b H hH z hz]
        rfl
      have hfi : ∀ i, ‖iteratedFDerivWithin ℝ b
          (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U z₀‖ ≤
            2 ^ b * T := by
        intro i
        refine ((ContinuousLinearMap.smulRightL ℝ V E).norm_iteratedFDerivWithin_le_of_bilinear
          (hc i b) (hG i) hU.uniqueDiffOn hz₀ le_rfl).trans ?_
        have hsum : ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) *
            ‖iteratedFDerivWithin ℝ j (c i) U z₀‖ *
            ‖iteratedFDerivWithin ℝ (b - j) (fun z => Dop i H (Γ z)) U z₀‖ ≤
              ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * T := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hcj : ‖iteratedFDerivWithin ℝ j (c i) U z₀‖ ≤ Kc * M ^ (j + 1) := by
            rw [iteratedFDerivWithin_of_isOpen j hU hz₀]
            exact hcb i j (by omega)
          have hGj : ‖iteratedFDerivWithin ℝ (b - j) (fun z => Dop i H (Γ z)) U z₀‖ ≤
              R ^ (b - j) * (β * lam) * (lam * M) ^ (b - j) := by
            rw [iteratedFDerivWithin_of_isOpen (b - j) hU hz₀]
            refine ih (b - j) (by omega) (by omega) (Dop i H) (β * lam)
              (hmono _ _ _ (Nat.sub_le b j) (hDop b H i hH)) fun w hw' => ?_
            have h := hw (w ++ [i]) (by rw [List.length_append, List.length_singleton]; omega)
            simp only [List.foldr_append, List.foldr_cons, List.foldr_nil, List.length_append,
              List.length_singleton] at h
            calc _ ≤ β * lam ^ (w.length + 1) := h
              _ = β * lam * lam ^ w.length := by ring
          calc ‖iteratedFDerivWithin ℝ j (c i) U z₀‖ *
                ‖iteratedFDerivWithin ℝ (b - j) (fun z => Dop i H (Γ z)) U z₀‖
              ≤ (Kc * M ^ (j + 1)) * (R ^ (b - j) * (β * lam) * (lam * M) ^ (b - j)) :=
                mul_le_mul hcj hGj (norm_nonneg _) (mul_nonneg hKc (pow_nonneg hM0 _))
            _ ≤ T := by
                rw [hT]
                exact mul_pow_mul_le_mul_pow_succ (by omega) hKc hR hβ hlam hM
        calc _ ≤ 1 * ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) * T :=
              mul_le_mul (norm_smulRightL_le E) hsum
                (Finset.sum_nonneg fun j _ => by positivity) zero_le_one
          _ = 2 ^ b * T := by
              rw [one_mul, ← Finset.sum_mul]
              congr 1
              exact_mod_cast Nat.sum_range_choose b
      have hN : (Fintype.card I : ℝ) * Kc * 2 ^ b ≤ R := by
        have h2 : (2 : ℝ) ^ b ≤ 2 ^ q := pow_le_pow_right_of_one_le (by norm_num) (by omega)
        calc _ ≤ (Fintype.card I : ℝ) * Kc * 2 ^ q := mul_le_mul_of_nonneg_left h2 hNK
          _ ≤ R := by
              rw [hRdef, add_mul, one_mul]
              exact le_add_of_nonneg_right (pow_nonneg (by norm_num) q)
      have hX : 0 ≤ R ^ b * β * (lam * M) ^ (b + 1) :=
        mul_nonneg (mul_nonneg (pow_nonneg hR0 _) hβ) (pow_nonneg (mul_nonneg hlam0 hM0) _)
      calc ‖iteratedFDeriv ℝ (b + 1) (fun z => H (Γ z)) z₀‖
          = ‖iteratedFDerivWithin ℝ b
              (∑ i, fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z)))
              U z₀‖ := by
            rw [← norm_iteratedFDeriv_fderiv,
              ← (iteratedFDerivWithin_of_isOpen b hU hz₀ :
                iteratedFDerivWithin ℝ b (fderiv ℝ (fun z => H (Γ z))) U z₀ =
                  iteratedFDeriv ℝ b (fderiv ℝ (fun z => H (Γ z))) z₀),
              iteratedFDerivWithin_congr heq hz₀]
        _ = ‖∑ i, iteratedFDerivWithin ℝ b
              (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U z₀‖ := by
            rw [iteratedFDerivWithin_sum_apply hU.uniqueDiffOn hz₀ fun i _ => hf i z₀ hz₀]
        _ ≤ ∑ i, ‖iteratedFDerivWithin ℝ b
              (fun z => ContinuousLinearMap.smulRightL ℝ V E (c i z) (Dop i H (Γ z))) U z₀‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _i : I, 2 ^ b * T := Finset.sum_le_sum fun i _ => hfi i
        _ = (Fintype.card I : ℝ) * (2 ^ b * T) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = ((Fintype.card I : ℝ) * Kc * 2 ^ b) * (R ^ b * β * (lam * M) ^ (b + 1)) := by
            rw [hT]; ring
        _ ≤ R * (R ^ b * β * (lam * M) ^ (b + 1)) := mul_le_mul_of_nonneg_right hN hX
        _ = R ^ (b + 1) * β * (lam * M) ^ (b + 1) := by ring
  intro b hb H β hH hw
  have h0 : ‖H (Γ z₀)‖ ≤ β := by simpa using hw [] (Nat.zero_le _)
  have hβ : 0 ≤ β := (norm_nonneg _).trans h0
  calc _ ≤ R ^ b * β * (lam * M) ^ b := key b hb H β hH hw
    _ ≤ R ^ q * β * (lam * M) ^ b :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right_of_one_le hR hb) hβ)
          (pow_nonneg (mul_nonneg hlam0 hM0) _)

end words

end PI.UnitaryGroupMassFormula.UsCost.ZI

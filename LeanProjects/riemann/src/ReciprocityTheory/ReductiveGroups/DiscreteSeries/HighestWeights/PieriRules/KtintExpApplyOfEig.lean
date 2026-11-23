import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma ktint_exp_apply_of_eig {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (c : ℂ) (v : E) (h : A v = c • v) :
    NormedSpace.exp A v = NormedSpace.exp c • v := by
  have hpow : ∀ k : ℕ, (A ^ k) v = c ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      show (A ^ k) (A v) = _
      rw [h, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hA := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hc := NormedSpace.expSeries_summable' (𝕂 := ℂ) c
  have e1 : NormedSpace.exp A = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • A ^ k :=
    congr_fun (NormedSpace.exp_eq_tsum ℂ) A
  have e2 : NormedSpace.exp c = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • c ^ k :=
    congr_fun (NormedSpace.exp_eq_tsum ℂ) c
  rw [e1, e2]
  have e3 := ContinuousLinearMap.map_tsum (ContinuousLinearMap.apply ℂ E v) hA
  simp only [ContinuousLinearMap.apply_apply] at e3
  rw [e3]
  simp only [_root_.smul_apply, hpow, smul_smul]
  exact Summable.tsum_smul_const hc v

lemma ktint_inK (ε : Fin n → Bool) (a : Fin n) :
    inK ε (Complex.I • Matrix.single a a (1 : ℂ)) := by
  have hc : Commute (Complex.I • Matrix.single a a (1 : ℂ)) (Jm ε) := by
    apply Commute.smul_left
    ext i j
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
    by_cases h : a = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · simp [h]
  refine ⟨?_, hc.eq⟩
  unfold inG
  have hs : (Complex.I • Matrix.single a a (1 : ℂ))ᴴ = -(Complex.I • Matrix.single a a (1 : ℂ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_single, star_one, Complex.star_def,
      Complex.conj_I, neg_smul]
  rw [hs, Matrix.neg_mul, hc.eq, neg_add_cancel]

lemma ktint_exp_two_pi (a : Fin n) :
    NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • (Complex.I • Matrix.single a a (1 : ℂ))) =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hd : ((2 * Real.pi : ℝ) : ℂ) • (Complex.I • Matrix.single a a (1 : ℂ)) =
      Matrix.diagonal (fun i => if i = a then 2 * (Real.pi : ℂ) * Complex.I else 0) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases h : a = i ∧ a = j
    · obtain ⟨rfl, rfl⟩ := h
      push_cast
      simp only [and_self, if_true, mul_one]
    · rw [if_neg h]
      by_cases hij : i = j
      · subst hij
        have hia : i ≠ a := fun e => h ⟨e.symm, e.symm⟩
        simp [hia]
      · simp [hij]
  rw [hd, Matrix.exp_diagonal, Pi.exp_def, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = a
  · simp only [hi, if_true, ← Complex.exp_eq_exp_ℂ, Complex.exp_two_pi_mul_I]
  · simp only [hi, if_false, NormedSpace.exp_zero]

theorem kType_int {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : ∀ a, ∃ m : ℤ, Λ a = m := by
  intro a
  have hX := ktint_inK ε a
  obtain ⟨γ, hγ⟩ := exists_curve ε hX
  have hop := KType.op_curve T hX γ hγ (2 * Real.pi)
  have h1 : γ (2 * Real.pi) = 1 := by
    apply onep_KG_ext
    rw [hγ, ktint_exp_two_pi]
    rfl
  have hw : (((2 * Real.pi : ℝ) : ℂ) • T.dτ (Complex.I • Matrix.single a a (1 : ℂ))) T.w =
      (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (Λ a : ℂ))) • T.w := by
    rw [_root_.smul_apply, map_smul, _root_.smul_apply, T.w_wt, smul_smul, smul_smul, mul_assoc]
  have key := ktint_exp_apply_of_eig _ _ _ hw
  rw [← hop, h1] at key
  have hone : T.op 1 = 1 := by
    simp [KType.op]
  rw [hone] at key
  change T.w = _ at key
  have hw0 : T.w ≠ 0 := by
    intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have he : NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (Λ a : ℂ))) = 1 := by
    by_contra hne
    have h2 : (1 - NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (Λ a : ℂ)))) • T.w = 0 := by
      rw [sub_smul, one_smul, ← key, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact hne (sub_eq_zero.mp h3).symm
    · exact hw0 h3
  rw [← Complex.exp_eq_exp_ℂ, Complex.exp_eq_one_iff] at he
  obtain ⟨m, hm⟩ := he
  refine ⟨m, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have h4 : (Λ a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [← hm]
    push_cast
    ring
  have h5 : (Λ a : ℂ) = ((m : ℝ) : ℂ) := by
    rw [mul_right_cancel₀ hpi h4]
    push_cast
    rfl
  exact_mod_cast h5

end ReciprocityTheory.ChartRestriction.DS.HW

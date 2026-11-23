import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrCap

theorem exp_eig {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (A : W →L[ℂ] W) (μ : ℂ)
    (x : W) (hx : A x = μ • x) : NormedSpace.exp A x = Complex.exp μ • x := by
  have hpow : ∀ n : ℕ, (A ^ n) x = μ ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      show (A ^ n) (A x) = _
      rw [hx, map_smul, ih, smul_smul, pow_succ, mul_comm]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum ℂ (𝔸 := W →L[ℂ] W), NormedSpace.exp_eq_tsum ℂ (𝔸 := ℂ)]
  simp only
  have h := (ContinuousLinearMap.apply ℂ W x).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)
  simp only [ContinuousLinearMap.apply_apply] at h
  rw [h]
  simp only [_root_.smul_apply, hpow, smul_smul]
  rw [← (NormedSpace.expSeries_summable' (𝕂 := ℂ) μ).tsum_smul_const x]
  simp only [smul_eq_mul]

theorem exp_sum_eig {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] {k : ℕ}
    (T : Fin k → (W →L[ℂ] W)) (θ μ : Fin k → ℝ) (x : W) (hx : ∀ c, T c x = (μ c : ℂ) • x) :
    NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • T c) x = Complex.exp (((∑ c, μ c * θ c : ℝ) : ℂ) * Complex.I) • x := by
  rw [exp_eig _ (∑ c, ((θ c : ℂ) * Complex.I) * (μ c : ℂ)) x]
  · congr 2
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    ring
  · rw [_root_.sum_apply, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro c _
    rw [_root_.smul_apply, hx, smul_smul]

theorem lowK_allPos (k : ℕ) (u : Fin k → ℝ) (j : Fin k) :
    PI.UpqRep.lowK (PI.UpqRep.allPos k) u j = u j - ((k : ℝ) - 1) / 2 + (j : ℕ) := by
  have hj := j.isLt
  unfold PI.UpqRep.lowK PI.UpqRep.rhoN PI.UpqRep.rhoC PI.UpqRep.allPos
  simp only [Pi.add_apply, Pi.sub_apply, ne_eq, not_true_eq_false, and_false, and_true]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio]
  rw [Nat.sub_sub, Nat.cast_sub (by omega)]
  push_cast
  ring

theorem deriv_cexp {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (L : ℝ) (v : W) :
    HasDerivAt (fun t : ℝ => Complex.exp (((-t * L : ℝ) : ℂ) * Complex.I) • v) ((-(L : ℂ) * Complex.I) • v) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => -t * L) (-L) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).neg).mul_const L
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => (((-t * L : ℝ) : ℂ) * Complex.I)) (((-L : ℝ) : ℂ) * Complex.I) 0 :=
    h1.ofReal_comp.mul_const Complex.I
  have h3 := (h2.cexp).smul_const v
  convert h3 using 1
  simp

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem lie_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (X : ι → Mx k r) (hX : ∀ i, InLieW k r z (X i)) :
    InLieW k r z (∑ i ∈ s, ((c i : ℝ) : ℂ) • X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (LieBracketMultiplication.lie_zero (k := k) (r := r) (z := z))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact LieBracketMultiplication.lie_add (LieBracketMultiplication.lie_smul (hX a) _) ih

theorem dOp_sum (hR : IsRepW k r z π) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (X : ι → Mx k r)
    (hX : ∀ i, InLieW k r z (X i)) : dOp π (∑ i ∈ s, ((c i : ℝ) : ℂ) • X i) = ∑ i ∈ s, c i • dOp π (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SkewHermitianParts.dOp_zero π
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      (differential_operator_linear W k r z π hR _ _ (LieBracketMultiplication.lie_smul (hX a) (c a)) (lie_sum s c X hX)).1,
      (differential_operator_linear W k r z π hR _ _ (hX a) (hX a)).2 (c a), ih]

theorem op_torus (hR : IsRepW k r z π) {Bs : Fin k → Fin (2 * r + k + 1) → ℂ} (hB : IsFrameOf k r [z] Bs)
    (θ : Fin k → ℝ) :
    π (NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • unitB (Hpk k r) Bs c c)) =
      NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • ecOp π (unitB (Hpk k r) Bs c c)) := by
  set A : Fin k → Mx k r := fun c => hpart2 (Hpk k r) (unitB (Hpk k r) Bs c c) with hAdef
  have hA : ∀ c, InLieW k r z (A c) := fun c => (QrD.frame_lie hB c c).2
  have hAe : ∀ c, A c = (-Complex.I) • unitB (Hpk k r) Bs c c := fun c => hpart2_self Bs c
  have hY : ∑ c, ((θ c : ℂ) * Complex.I) • unitB (Hpk k r) Bs c c =
      ((1 : ℝ) : ℂ) • ∑ c, ((-θ c : ℝ) : ℂ) • A c := by
    rw [Complex.ofReal_one, one_smul]
    apply Finset.sum_congr rfl
    intro c _
    rw [hAe c, smul_smul]
    congr 1
    push_cast
    ring
  have hec : ∀ c, ecOp π (unitB (Hpk k r) Bs c c) = Complex.I • dOp π (A c) := by
    intro c
    unfold ecOp
    rw [hpart1_self, SkewHermitianParts.dOp_zero, zero_add]
  rw [hY, representation_exp W k r z π hR _ (lie_sum _ _ _ hA) 1, one_smul, dOp_sum hR _ _ _ hA]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  rw [hec c, ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  linear_combination (-(θ c : ℂ)) * Complex.I_sq

end Rep

end QrCap

end Formalism.FourierDecayAlt.P

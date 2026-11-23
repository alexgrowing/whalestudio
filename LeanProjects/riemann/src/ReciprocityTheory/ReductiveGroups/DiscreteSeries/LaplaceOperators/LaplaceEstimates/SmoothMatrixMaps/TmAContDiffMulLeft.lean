import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LholClmEventually
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TmASmSum

noncomputable section

open Matrix
open scoped ContDiff InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

section Calc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem tmA_eword_congr {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (e : ∀ x, Formalism.REAL.inUJ ε x → f x = h x) :
    ∀ (w : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε w f g = Formalism.REAL.Eword ε w h g
  | [], g, hg => e g hg
  | p :: w, g, hg => by
      simp only [Formalism.REAL.Eword]
      exact Formalism.REAL.lie_derivative_congr p.1 p.2 (fun x hx => tmA_eword_congr e w x hx) hg

theorem tmA_eword_lin {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    (hh : Formalism.REAL.SmoothOnG ε h) (c : ℂ) :
    ∀ (w : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε w (fun x => f x + c * h x) g = Formalism.REAL.Eword ε w f g + c * Formalism.REAL.Eword ε w h g
  | [], g, _ => rfl
  | p :: w, g, hg => by
      simp only [Formalism.REAL.Eword]
      rw [Formalism.REAL.lie_derivative_congr (h := fun x => Formalism.REAL.Eword ε w f x + c * Formalism.REAL.Eword ε w h x) p.1 p.2
        (fun x hx => tmA_eword_lin hf hh c w x hx) hg]
      exact Formalism.REAL.lie_derivative_add_smul p.1 p.2 c (Formalism.REAL.smooth_iterated_lie_derivative hf w) (Formalism.REAL.smooth_iterated_lie_derivative hh w) hg

theorem tmA_eword_zero :
    ∀ (w : List (Fin n × Fin n)) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε w (fun _ => (0 : ℂ)) g = 0
  | [], _, _ => rfl
  | p :: w, g, hg => by
      simp only [Formalism.REAL.Eword]
      rw [Formalism.REAL.lie_derivative_congr (h := fun _ => (0 : ℂ)) p.1 p.2 (fun x hx => tmA_eword_zero w x hx) hg]
      exact Formalism.REAL.lie_derivative_const_zero _ _ _

theorem tmA_eword_left (x : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    ∀ w : List (Fin n × Fin n),
      Formalism.REAL.Eword ε w (fun g => f (x * g)) = fun g => Formalism.REAL.Eword ε w f (x * g)
  | [] => rfl
  | p :: w => by
      simp only [Formalism.REAL.Eword]
      rw [tmA_eword_left x f w]
      funext g
      simp only [Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd, Matrix.mul_assoc]

theorem tmA_inUJ_mul {x g : Matrix (Fin n) (Fin n) ℂ} (hx : Formalism.REAL.inUJ ε x) (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (x * g) := by
  unfold Formalism.REAL.inUJ at *
  rw [Matrix.conjTranspose_mul,
    show gᴴ * xᴴ * Formalism.REAL.Jm ε * (x * g) = gᴴ * (xᴴ * Formalism.REAL.Jm ε * x) * g by
      simp only [Matrix.mul_assoc], hx, hg]

theorem tmA_inv_eq {x : Matrix (Fin n) (Fin n) ℂ} (hx : Formalism.REAL.inUJ ε x) :
    x⁻¹ = Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε := by
  apply Matrix.inv_eq_left_inv
  unfold Formalism.REAL.inUJ at hx
  rw [show Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε * (xᴴ * Formalism.REAL.Jm ε * x) by
    simp only [Matrix.mul_assoc], hx, Formalism.REAL.Jm_mul_self]

theorem tmA_mul_inv {x : Matrix (Fin n) (Fin n) ℂ} (hx : Formalism.REAL.inUJ ε x) : x * x⁻¹ = 1 := by
  have h : Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε * x = 1 := by
    unfold Formalism.REAL.inUJ at hx
    rw [show Formalism.REAL.Jm ε * xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε * (xᴴ * Formalism.REAL.Jm ε * x) by
      simp only [Matrix.mul_assoc], hx, Formalism.REAL.Jm_mul_self]
  exact Matrix.mul_nonsing_inv x (Matrix.isUnit_det_of_left_inverse h)

theorem tmA_inUJ_inv {x : Matrix (Fin n) (Fin n) ℂ} (hx : Formalism.REAL.inUJ ε x) : Formalism.REAL.inUJ ε x⁻¹ := by
  have h1 := tmA_mul_inv hx
  rw [tmA_inv_eq hx] at h1 ⊢
  unfold Formalism.REAL.inUJ
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Formalism.REAL.Jm_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have hJJ : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.one_mul]
  simp only [Matrix.mul_assoc] at h1 ⊢
  rw [hJJ, h1, Matrix.mul_one]

theorem tmA_contDiff_mulLeft (x : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ (fun g : Matrix (Fin n) (Fin n) ℂ => x * g) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply_apply ℝ ℂ k j)

theorem tmA_sm_left {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : Formalism.REAL.inUJ ε x) : Formalism.REAL.SmoothOnG ε (fun g => f (x * g)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (x * g₀) (tmA_inUJ_mul hx hg₀)
  have hL := tmA_contDiff_mulLeft x
  refine ⟨(fun g => x * g) ⁻¹' U, fun g => F (x * g), hU.preimage hL.continuous, hgU, ?_, ?_⟩
  · exact hF.comp hL.contDiffOn (fun g hg => hg)
  · intro g hg hgJ
    exact hfF (x * g) hg (tmA_inUJ_mul hx hgJ)

theorem tmA_sm_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i ∈ s, Formalism.REAL.SmoothOnG ε (F i)) : Formalism.REAL.SmoothOnG ε (fun x => ∑ i ∈ s, F i x) := by
  first | exact UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} .. | (apply UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} <;> assumption) | (apply @UpperTheory.Reformulated.B.Qf26.tmA_sm_sum.{u_1} <;> first | assumption | infer_instance)

theorem tmA_eab_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i ∈ s, Formalism.REAL.SmoothOnG ε (F i)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => ∑ i ∈ s, F i x) g = ∑ i ∈ s, Formalism.REAL.Eab ε a b (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.REAL.lie_derivative_const_zero (ε := ε) a b g
  | insert i s hi ih =>
      have hs : ∀ j ∈ s, Formalism.REAL.SmoothOnG ε (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
      have e : (fun x => ∑ j ∈ insert i s, F j x) = fun x => F i x + 1 * ∑ j ∈ s, F j x := by
        funext x; rw [Finset.sum_insert hi, one_mul]
      rw [e, Formalism.REAL.lie_derivative_add_smul a b 1 (hF i (Finset.mem_insert_self i s)) (tmA_sm_sum s F hs) hg,
        ih hs, one_mul, Finset.sum_insert hi]

end Calc

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra

variable {n : ℕ}

theorem tmA_frob_eq (A : Matrix (Fin n) (Fin n) ℂ) : frob A = ‖A‖ := S7.sqrt_hs_frobVG A

theorem tmA_frob_mul (A B : Matrix (Fin n) (Fin n) ℂ) : frob (A * B) ≤ frob A * frob B := by
  rw [tmA_frob_eq, tmA_frob_eq, tmA_frob_eq]
  exact Matrix.frobenius_norm_mul A B

end Frob

section Gen

variable {n : ℕ} {ε : Fin n → Bool}

theorem tmA_entry_le_frob (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ≤ frob g := by
  have h := Real.abs_le_sqrt (S7.hs_entry_leVG g i j)
  rw [abs_of_nonneg (norm_nonneg _)] at h
  exact h

theorem tmA_one_le_col {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (a : Fin n) :
    1 ≤ ∑ i, ‖g i a‖ ^ 2 := by
  have h := congrFun (congrFun hg a) a
  have h1 : ‖(gᴴ * Formalism.REAL.Jm ε * g) a a‖ = 1 := by
    rw [h]; unfold Formalism.REAL.Jm; rw [Matrix.diagonal_apply_eq]; split_ifs <;> simp
  have h2 : ‖(gᴴ * Formalism.REAL.Jm ε * g) a a‖ ≤ ∑ i, ‖g i a‖ ^ 2 := by
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    unfold Formalism.REAL.Jm
    rw [Matrix.mul_diagonal, norm_mul, norm_mul, Matrix.conjTranspose_apply, norm_star]
    split_ifs <;> simp [sq]
  linarith

theorem tmA_one_le_frob {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (a : Fin n) : 1 ≤ frob g := by
  unfold frob
  rw [Real.one_le_sqrt]
  refine (tmA_one_le_col hg a).trans ?_
  rw [Finset.sum_comm]
  exact Finset.single_le_sum (f := fun j => ∑ i, ‖g i j‖ ^ 2)
    (fun j _ => Finset.sum_nonneg fun i _ => by positivity) (Finset.mem_univ a)

theorem tmA_frob_trans {x₀ g : Matrix (Fin n) (Fin n) ℂ} (hx₀ : Formalism.REAL.inUJ ε x₀) (hg : Formalism.REAL.inUJ ε g)
    (a₀ : Fin n) {a : ℝ} (ha : 0 ≤ a) : frob (x₀⁻¹ * g) ^ (-a) ≤ frob x₀ ^ a * frob g ^ (-a) := by
  have hX := tmA_one_le_frob hx₀ a₀
  have hG := tmA_one_le_frob hg a₀
  have hle : frob g ≤ frob x₀ * frob (x₀⁻¹ * g) := by
    calc frob g = frob (x₀ * (x₀⁻¹ * g)) := by rw [← Matrix.mul_assoc, tmA_mul_inv hx₀, Matrix.one_mul]
      _ ≤ _ := tmA_frob_mul _ _
  have hq : frob g / frob x₀ ≤ frob (x₀⁻¹ * g) := by
    rw [div_le_iff₀ (by linarith)]; linarith
  calc frob (x₀⁻¹ * g) ^ (-a) ≤ (frob g / frob x₀) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (div_pos (by linarith) (by linarith)) hq (by linarith)
    _ = frob x₀ ^ a * frob g ^ (-a) := by
        rw [Real.div_rpow (by linarith) (by linarith), Real.rpow_neg (by linarith : (0:ℝ) ≤ frob x₀)]
        field_simp

end Gen

section Coef

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mat k r → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ D}

theorem tmB_rd_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {x₀ g X : Mat k r}
    (hy : x₀⁻¹ * g ∈ UJset ε) (hX : inG ε X) (w : H) (m : D) :
    Formalism.REAL.Rd X (coefX σ x₀ w (m : H)) g = coefX σ x₀ w ((actM E X m : D) : H) g := by
  set L : H →L[ℝ] ℂ := ((innerSL ℂ w).comp (σ (x₀⁻¹ * g))).restrictScalars ℝ with hL
  have h1 : (fun t : ℝ => coefX σ x₀ w (m : H) (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => L (σ (NormedSpace.exp ((t : ℂ) • X)) (m : H)) := by
    funext t
    simp only [coefX, ← Matrix.mul_assoc]
    rw [hσ.1.2 _ hy _ (exp_smul_mem_UJset hX t)]
    simp [hL, innerSL_apply_apply]
  have h2 := (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hD.deriv X hX m)).deriv
  simp only [Function.comp_def] at h2
  unfold Formalism.REAL.Rd
  rw [h1, h2]
  simp [hL, coefX, innerSL_apply_apply]

theorem tmB_eab_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) {x₀ g : Mat k r}
    (hy : x₀⁻¹ * g ∈ UJset ε) (w : H) (m : D) (a b : Fin (2 * r + k + 1)) :
    Formalism.REAL.Eab ε a b (coefX σ x₀ w (m : H)) g = coefX σ x₀ w ((E a b m : D) : H) g := by
  rw [Formalism.REAL.lie_derivative_def,
    tmB_rd_coef (X := Formalism.REAL.cpart1 ε (Matrix.single a b 1)) hσ hD hy (Formalism.REAL.real_part_single_mem ε a b) w m,
    tmB_rd_coef (X := Formalism.REAL.cpart2 ε (Matrix.single a b 1)) hσ hD hy (Formalism.REAL.imaginary_part_single_mem ε a b) w m]
  have hZ := (Formalism.REAL.complex_parts_mem_lie_algebra_holds _ ε (Matrix.single a b 1)).2.2.1
  have key : E a b = actM E (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) +
      Complex.I • actM E (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) := by
    rw [← actM_single' E a b, ← actM_smul', ← actM_add', ← hZ]
  rw [key]
  simp [coefX]

end Coef

end ReciprocityTheory.ChartRestriction.DS.Lap

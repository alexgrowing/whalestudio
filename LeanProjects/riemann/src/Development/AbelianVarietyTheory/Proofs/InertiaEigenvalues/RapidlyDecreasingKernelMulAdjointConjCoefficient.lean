import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

namespace RapidCoef

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * ‖toL A‖ * ‖toL B‖ := by
  have h : ∀ (C : Matrix (Fin a) (Fin a) (Cinf E)) i j, ‖C i j‖ ≤ ‖toL C‖ := fun C i j =>
    (norm_le_pi_norm (toL C i) j).trans (norm_le_pi_norm (toL C) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin a, ‖toL A‖ * ‖toL B‖ := Finset.sum_le_sum fun l _ =>
        (norm_mul_le _ _).trans (mul_le_mul (h A i l) (h B l j) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp [mul_assoc]

theorem continuous_smul_adj : Continuous fun q : Cinf E × Lie E a => toL (q.1 • (Matrix.of q.2).adjugate) := by
  change Continuous fun q : Cinf E × Matrix (Fin a) (Fin a) (Cinf E) => q.1 • q.2.adjugate
  fun_prop

theorem continuous_conj (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    Continuous fun q : Lie E a × Lie E a => toL (Matrix.of q.1 * M * Matrix.of q.2) := by
  change Continuous fun q : Matrix (Fin a) (Fin a) (Cinf E) × Matrix (Fin a) (Fin a) (Cinf E) => q.1 * M * q.2
  fun_prop

theorem inv_val_eq (y : GL (Fin a) (Cinf E)) :
    (y⁻¹).val = (fun v => (y.val.det v)⁻¹) • y.val.adjugate := by
  symm
  apply Units.eq_inv_of_mul_eq_one_left
  rw [mul_smul_comm, Matrix.mul_adjugate, smul_smul]
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have : (fun v => (y.val.det v)⁻¹) * y.val.det = 1 := by
    funext v
    exact inv_mul_cancel₀ ((Pi.isUnit_iff.1 hu) v).ne_zero
  rw [this, one_smul]

end RapidCoef

open RapidCoef in

theorem isRapidInf_mul_adCoef : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type)
    [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ →
      ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ := by
  intro E _ _ _ a X _ ν k γ hr p
  obtain ⟨hk, hγ, hint⟩ := hr
  haveI : SecondCountableTopology (Lie E a) := inferInstance
  haveI : BorelSpace (Lie E a) := inferInstance
  haveI : OpensMeasurableSpace (Lie E a × Lie E a) := inferInstance
  haveI : OpensMeasurableSpace (Cinf E × Lie E a) := inferInstance
  have hA : Measurable fun x => toL (γ x).val := hγ
  have hdet : Measurable fun x => ((γ x).val).det := contDiff_det.continuous.measurable.comp hA
  have hc : Measurable fun x => (fun v => (((γ x).val).det v)⁻¹ : Cinf E) :=
    measurable_pi_lambda _ fun v => ((measurable_pi_apply v).comp hdet).inv
  have hinv : Measurable fun x => toL (γ x)⁻¹.val := by
    have : (fun x => toL (γ x)⁻¹.val) =
        (fun q : Cinf E × Lie E a => toL (q.1 • (Matrix.of q.2).adjugate)) ∘
          fun x => ((fun v => (((γ x).val).det v)⁻¹ : Cinf E), toL (γ x).val) := by
      funext x; simp only [Function.comp_apply, inv_val_eq]; rfl
    rw [this]
    exact continuous_smul_adj.measurable.comp (hc.prodMk hA)
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin a) (Fin a) (Cinf E), M = Matrix.of (lieBasis E a p.2) := ⟨_, rfl⟩
  have e : ∀ y : GL (Fin a) (Cinf E), adCoef y p = lieCoord E a p.1 (toL ((y⁻¹).val * M * y.val)) :=
    fun y => by subst hM; rfl
  have hconj : Measurable fun x => toL ((γ x)⁻¹.val * M * (γ x).val) := by
    have h := (continuous_conj M).measurable.comp (hinv.prodMk hA)
    exact h
  have had : Measurable fun x => adCoef (γ x) p := by
    have h := (lieCoord E a p.1).continuous.measurable.comp hconj
    have h' : (fun x => adCoef (γ x) p) = fun x => lieCoord E a p.1 (toL ((γ x)⁻¹.val * M * (γ x).val)) :=
      funext fun x => e (γ x)
    rw [h']
    exact h
  have hh : Measurable fun x => height (γ x) := by
    unfold height
    exact (measurable_const.add hA.norm).add hinv.norm
  have hh1 : ∀ y : GL (Fin a) (Cinf E), 1 ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL y.val), norm_nonneg (toL (y⁻¹).val)]
  have hA_le : ∀ y : GL (Fin a) (Cinf E), ‖toL y.val‖ ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have hI_le : ∀ y : GL (Fin a) (Cinf E), ‖toL (y⁻¹).val‖ ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL y.val)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ‖lieCoord E a p.1‖ * ((a : ℝ) * (a * ‖toL M‖)) := ⟨_, rfl⟩
  have hbd : ∀ y : GL (Fin a) (Cinf E), ‖adCoef y p‖ ≤ C * height y ^ 2 := fun y => by
    have h0 : 0 ≤ height y := zero_le_one.trans (hh1 y)
    have h1 : ‖toL ((y⁻¹).val * M * y.val)‖ ≤ a * (a * ‖toL (y⁻¹).val‖ * ‖toL M‖) * ‖toL y.val‖ :=
      (norm_toL_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_toL_mul_le _ _) (Nat.cast_nonneg _)) (norm_nonneg _))
    have h2 : a * (a * ‖toL (y⁻¹).val‖ * ‖toL M‖) * ‖toL y.val‖ ≤ a * (a * height y * ‖toL M‖) * height y :=
      mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hI_le y) (Nat.cast_nonneg _)) (norm_nonneg _)) (Nat.cast_nonneg _))
        (hA_le y) (norm_nonneg _) (by positivity)
    rw [e]
    calc ‖lieCoord E a p.1 (toL ((y⁻¹).val * M * y.val))‖ ≤ ‖lieCoord E a p.1‖ * ‖toL ((y⁻¹).val * M * y.val)‖ :=
          (lieCoord E a p.1).le_opNorm _
      _ ≤ ‖lieCoord E a p.1‖ * (a * (a * height y * ‖toL M‖) * height y) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
      _ = C * height y ^ 2 := by rw [hC]; ring
  refine ⟨hk.mul had, hγ, fun N => ?_⟩
  refine ((hint (N + 2)).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((hk.mul had).norm.mul (hh.pow_const N)).aestronglyMeasurable
  · have hpos : 0 ≤ height (γ x) ^ N := pow_nonneg (zero_le_one.trans (hh1 _)) N
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hpos), norm_mul]
    calc ‖k x‖ * ‖adCoef (γ x) p‖ * height (γ x) ^ N
        ≤ ‖k x‖ * (C * height (γ x) ^ 2) * height (γ x) ^ N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _)) hpos
      _ = C * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring

end GlobalTheory.JSW

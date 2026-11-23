import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens.Deriv

def dg (k r : ℕ) (c : Fin r → ℂ) (j : Fin (2 * r + k + 1)) : ℂ :=
  if hj : j.val < r then c ⟨j.val, hj⟩
  else if hj2 : j.val ≤ r + k then 1
  else (star (c ⟨2 * r + k - j.val, by omega⟩))⁻¹

theorem bigCell_eq (k r : ℕ) (c : Fin r → ℂ) :
    bigCell k r c 1 = wC k r * Matrix.diagonal (dg k r c) := by
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [wC, bigCell, dg]
  split_ifs <;> simp

def sg (k r : ℕ) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if j.val < r ∨ r + k < j.val then ⟨2 * r + k - j.val, by omega⟩ else j

theorem sg_sg (k r : ℕ) (j : Fin (2 * r + k + 1)) : sg k r (sg k r j) = j := by
  have := j.isLt
  have hv : ∀ i : Fin (2 * r + k + 1), (sg k r i).val =
      if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
    intro i; simp only [sg]; split_ifs <;> rfl
  apply Fin.ext
  rw [hv, hv]
  split_ifs <;> omega

theorem wC_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    wC k r i j = if i = sg k r j then 1 else 0 := by
  have := j.isLt
  have := i.isLt
  have hv : (sg k r j).val =
      if j.val < r ∨ r + k < j.val then 2 * r + k - j.val else j.val := by
    simp only [sg]; split_ifs <;> rfl
  simp only [wC, bigCell, esI, Matrix.one_apply, Fin.ext_iff, hv, star_one, inv_one]
  split_ifs <;> first | rfl | omega

theorem wC_mul_wC (k r : ℕ) : wC k r * wC k r = 1 := by
  ext i j
  simp only [Matrix.mul_apply, wC_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (sg k r j)]
  · simp [sg_sg]
  · intro b _ hb; simp [hb]
  · simp

def umL {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : lieE S →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := um
  map_add' X Y := by ext i j; apply Complex.ext <;> simp [um, unrealify]
  map_smul' a X := by ext i j; apply Complex.ext <;> simp [um, unrealify]

theorem dg_one (k r : ℕ) : dg k r (fun a => 1 + (0 : Fin r → ℂ) a) = fun _ => 1 := by
  funext j; simp only [dg]; split_ifs <;> simp

theorem dg_contOn (k r : ℕ) (j : Fin (2 * r + k + 1)) :
    ContinuousOn (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a) j) (Metric.ball 0 1) := by
  simp only [dg]
  split_ifs with h1 h2
  · fun_prop
  · fun_prop
  · apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [mem_ball_zero_iff] at hx
    have h3 := (norm_le_pi_norm x ⟨2 * r + k - j.val, by omega⟩).trans_lt hx
    rw [star_ne_zero]
    intro h
    have : x ⟨2 * r + k - j.val, by omega⟩ = -1 := by linear_combination h
    rw [this] at h3
    simp at h3

theorem dg_deriv (k r : ℕ) (j : Fin (2 * r + k + 1)) :
    ∃ D : (Fin r → ℂ) →L[ℝ] ℂ,
      HasStrictFDerivAt (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a) j) D 0 ∧
      ∀ x, D x = torD k r x j j := by
  simp only [dg, torD, Matrix.diagonal_apply_eq]
  by_cases h1 : j.val < r
  · simp only [dif_pos h1]
    exact ⟨_, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ)
      ⟨j.val, h1⟩).hasStrictFDerivAt.const_add 1, fun x => rfl⟩
  · by_cases h2 : j.val ≤ r + k
    · simp only [dif_neg h1, dif_pos h2, dif_neg (not_lt.2 h2)]
      exact ⟨0, hasStrictFDerivAt_const _ _, fun x => rfl⟩
    · simp only [dif_neg h1, dif_neg h2, dif_pos (not_le.1 h2)]
      set a : Fin r := ⟨2 * r + k - j.val, by omega⟩
      let L : (Fin r → ℂ) →L[ℝ] ℂ := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) a)
      have hL : HasStrictFDerivAt (fun x : Fin r → ℂ => 1 + L x) L 0 := L.hasStrictFDerivAt.const_add 1
      have hi : HasStrictDerivAt (fun z : ℂ => z⁻¹) (-((1 + L 0) ^ 2)⁻¹) (1 + L 0) :=
        hasStrictDerivAt_inv (by simp)
      have := (hi.hasStrictFDerivAt.restrictScalars ℝ).comp (0 : Fin r → ℂ) hL
      refine ⟨_, this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_), fun x => ?_⟩
      · simp [L]
      · simp [L]

theorem torD_eq (k r : ℕ) (x : Fin r → ℂ) : torD k r x = Matrix.diagonal fun j => torD k r x j j := by
  simp only [torD, Matrix.diagonal_apply_eq]

theorem um_zero {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : um (0 : lieE S) = 0 := (umL S).map_zero

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_um_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (L : E →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    HasStrictFDerivAt (fun v => NormedSpace.exp (L v)) (LinearMap.toContinuousLinearMap L) 0 := by
  have h1 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin m) (Fin m) ℂ → _)
      (1 : Matrix (Fin m) (Fin m) ℂ →L[ℝ] Matrix (Fin m) (Fin m) ℂ)
      (LinearMap.toContinuousLinearMap L 0) := by
    rw [map_zero]; exact hasStrictFDerivAt_exp_zero
  exact h1.comp 0 (LinearMap.toContinuousLinearMap L).hasStrictFDerivAt

theorem exp_um_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ}
    (L : E →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    Continuous (fun v => NormedSpace.exp (L v)) :=
  NormedSpace.exp_continuous.comp (LinearMap.toContinuousLinearMap L).continuous

theorem diag_deriv (k r : ℕ) :
    ∃ D : (Fin r → ℂ) →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      HasStrictFDerivAt (fun x : Fin r → ℂ => Matrix.diagonal (dg k r (fun a => 1 + x a))) D 0 ∧
      ∀ x, D x = torD k r x := by
  choose D hD hD' using dg_deriv k r
  have h1 : HasStrictFDerivAt (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a))
      (ContinuousLinearMap.pi D) 0 := hasStrictFDerivAt_pi.2 hD
  let L : (Fin (2 * r + k + 1) → ℂ) →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin (2 * r + k + 1)) ℝ ℂ)
  refine ⟨_, L.hasStrictFDerivAt.comp 0 h1, fun x => ?_⟩
  rw [torD_eq]
  change Matrix.diagonal (fun j => D j x) = _
  simp only [hD']

theorem chart_deriv_mat (k r : ℕ) :
    ∃ D : EE k r →L[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      HasStrictFDerivAt (chart k r) D 0 ∧ ∀ v, D v = dchart k r v := by
  obtain ⟨D, hD, hD'⟩ := diag_deriv k r
  let P : EE k r →L[ℝ] (Fin r → ℂ) := (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  have h2 : HasStrictFDerivAt (fun v : EE k r => Matrix.diagonal (dg k r (fun a => 1 + v.2.1 a)))
      (D.comp P) 0 :=
    HasStrictFDerivAt.comp (0 : EE k r) (f := P) (by rw [map_zero]; exact hD) P.hasStrictFDerivAt
  have h1 := exp_um_deriv (E := EE k r)
    (-((umL (Nset k r)).comp ((LinearMap.fst ℝ _ _).comp (LinearMap.fst ℝ _ _))))
  have h3 := exp_um_deriv (E := EE k r)
    ((umL (Formalism.FourierDecayAlt.B2.UWb k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))
  have h4 := exp_um_deriv (E := EE k r)
    ((umL (Nset k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.fst ℝ _ _)))
  have h := (((h1.mul' (h2.const_mul (wC k r))).mul' h3).mul' h4).const_mul (wC k r)
  refine ⟨_, h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_), fun v => ?_⟩
  · simp only [chart, bigCell_eq]
    rfl
  · have e : dg k r (fun _ => 1) = fun _ => 1 := by simpa using dg_one k r
    simp [e, P, dchart, umL, um_zero]
    change wC k r * (wC k r * um v.1.2) + (wC k r * (wC k r * um v.2.2) +
      (wC k r * (wC k r * D v.2.1) + wC k r * (-um v.1.1 * wC k r))) = _
    simp only [hD', ← mul_assoc, wC_mul_wC, one_mul, mul_neg, neg_mul]
    abel

theorem chart_deriv (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ∃ D : EE k r →L[ℝ] ℂ, HasStrictFDerivAt (fun v => chart k r v i j) D 0 ∧
      ∀ v, D v = dchart k r v i j := by
  obtain ⟨D, hD, hD'⟩ := chart_deriv_mat k r
  let L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  refine ⟨_, L.hasStrictFDerivAt.comp 0 hD, fun v => ?_⟩
  change D v i j = _
  rw [hD']

theorem chart_contOn (k r : ℕ) : ContinuousOn (chart k r) (Metric.ball 0 1) := by
  have h1 := exp_um_cont (E := EE k r)
    (-((umL (Nset k r)).comp ((LinearMap.fst ℝ _ _).comp (LinearMap.fst ℝ _ _))))
  have h3 := exp_um_cont (E := EE k r)
    ((umL (Formalism.FourierDecayAlt.B2.UWb k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)))
  have h4 := exp_um_cont (E := EE k r)
    ((umL (Nset k r)).comp ((LinearMap.snd ℝ _ _).comp (LinearMap.fst ℝ _ _)))
  have h5 : ContinuousOn (fun x : Fin r → ℂ => dg k r (fun a => 1 + x a)) (Metric.ball 0 1) :=
    continuousOn_pi.2 (dg_contOn k r)
  have h6 : ContinuousOn (fun v : EE k r => dg k r (fun a => 1 + v.2.1 a)) (Metric.ball 0 1) := by
    refine h5.comp (f := fun v : EE k r => v.2.1) (by fun_prop) fun v hv => ?_
    rw [mem_ball_zero_iff] at hv ⊢
    exact ((norm_fst_le v.2).trans (norm_snd_le v)).trans_lt hv
  have h2 : ContinuousOn (fun v : EE k r => Matrix.diagonal (dg k r (fun a => 1 + v.2.1 a)))
      (Metric.ball 0 1) :=
    (Continuous.matrix_diagonal continuous_id).comp_continuousOn h6
  have h := (continuousOn_const (c := wC k r)).mul
    (((h1.continuousOn.mul ((continuousOn_const (c := wC k r)).mul h2)).mul h3.continuousOn).mul
      h4.continuousOn)
  refine h.congr fun v _ => ?_
  simp only [chart, bigCell_eq]
  rfl

end

theorem chart_zero (k r : ℕ) : chart k r 0 = 1 := by
  have e : dg k r (fun _ => 1) = fun _ => 1 := by simpa using dg_one k r
  simp [chart, bigCell_eq, um_zero, e, wC_mul_wC]

theorem chart_strict : ∀ (k r : ℕ), chart k r 0 = 1 ∧ ContinuousOn (chart k r) (Metric.ball 0 1) ∧
    ∀ i j, ∃ D : EE k r →L[ℝ] ℂ, HasStrictFDerivAt (fun v => chart k r v i j) D 0 ∧
      ∀ v, D v = dchart k r v i j :=
  fun k r => ⟨chart_zero k r, chart_contOn k r, chart_deriv k r⟩

end GlobalTheory.CellDens.Deriv

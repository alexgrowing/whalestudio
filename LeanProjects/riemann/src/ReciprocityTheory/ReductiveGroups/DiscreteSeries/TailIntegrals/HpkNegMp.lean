import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Phi2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.FixOfPerp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianFormBaseVectorRight

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace ThFin

theorem ga_nn (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : 0 ≤ Ga k r l Y := by
  unfold Ga
  open scoped ComplexOrder in
  have key : ∀ {m : ℕ} (W : Fin m → Fin (2 * r + k + 1) → ℂ),
      0 ≤ (Matrix.of fun a b => star (W a) ⬝ᵥ W b).det.re := by
    intro m W
    have h : (Matrix.of fun a b => star (W a) ⬝ᵥ W b) =
        (Matrix.of fun i a => W a i)ᴴ * Matrix.of fun i a => W a i := by
      ext a b
      simp [Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply]
    rw [h]
    exact (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self _).det_nonneg).1
  exact key _

theorem dot_unit {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (u v : Fin n → ℂ) :
    star (U *ᵥ u) ⬝ᵥ (U *ᵥ v) = star u ⬝ᵥ v := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

theorem ga_unit (k r : ℕ) (l : Fin (r + 1)) {U : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : Uᴴ * U = 1) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => U *ᵥ Y a) = Ga k r l Y := by
  unfold Ga
  simp only [dot_unit hU]

private lemma conjTranspose_Hpk_eq_Hpk (k r' : ℕ) : (Hpk k r')ᴴ = Hpk k r' := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | rfl | norm_num

private lemma Hpk_sq_eq_one (k r' : ℕ) : Hpk k r' * Hpk k r' = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hσ : (if (i : ℕ) < r' ∨ r' + k < (i : ℕ) then 2 * r' + k - i else (i : ℕ)) < 2 * r' + k + 1 := by
    split_ifs <;> omega
  rw [Finset.sum_eq_single ⟨_, hσ⟩]
  · simp only [Hpk, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | rfl | norm_num
  · intro l _ hl
    have h0 : Hpk k r' i l = 0 := by
      simp only [Hpk, Matrix.of_apply, ne_eq, Fin.ext_iff] at hl ⊢
      split_ifs at hl ⊢ <;> first | (exfalso; omega) | rfl
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem hpk_mem (k r' : ℕ) : Hpk k r' ∈ GV k r' := by
  simp only [GV, UH, Set.mem_setOf_eq]
  rw [conjTranspose_Hpk_eq_Hpk, Hpk_sq_eq_one, Matrix.one_mul]

theorem lev_conjT (k r' : ℕ) : (ιLev k 1 r' (Hpk k r'))ᴴ = ιLev k 1 r' (Hpk k r') := by
  have hc := conjTranspose_Hpk_eq_Hpk k r'
  ext p q
  rw [Matrix.conjTranspose_apply]
  unfold ιLev
  try dsimp only
  split_ifs <;> first | ((conv_rhs => rw [← hc]); rfl) | (simp; done) | (subst_vars; contradiction)

theorem lev_sq (k r' : ℕ) : ιLev k 1 r' (Hpk k r') * ιLev k 1 r' (Hpk k r') = 1 := by
  apply mat_eq_of_mulVec
  intro v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  have e : (fun j => (ιLev k 1 r' (Hpk k r') *ᵥ v) (levPos k 1 r' j)) =
      Hpk k r' *ᵥ fun j => v (levPos k 1 r' j) := by
    funext j
    rw [RankOneLeviIdentities.ιLev_mulVec, dif_pos ⟨Nat.le_add_left 1 j.val, by
      show j.val + 1 < 2 * r' + k + 1 + 1; omega⟩]
    congr 1
  ext p
  rw [RankOneLeviIdentities.ιLev_mulVec]
  split_ifs with h
  · rw [e, Hpk_mulVec_mulVec]
    exact congrArg v (Fin.ext (show p.val - 1 + 1 = p.val by omega))
  · rw [RankOneLeviIdentities.ιLev_mulVec, dif_neg h]

theorem lev_inv (k r' : ℕ) : (ιLev k 1 r' (Hpk k r'))⁻¹ = ιLev k 1 r' (Hpk k r') :=
  Matrix.inv_eq_left_inv (lev_sq k r')

theorem mv3 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A * A = 1) (v : Fin n → ℂ) :
    (A * B * A) *ᵥ (A *ᵥ v) = A *ᵥ (B *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (A * B), hA, Matrix.mul_one, ← Matrix.mulVec_mulVec]

theorem heis_eq (hCL : HeisConjLev) (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (s : ℝ) :
    heis0 k r' (y, s) =
      ιLev k 1 r' (Hpk k r') * heis0 k r' (Hpk k r' *ᵥ y, s) * ιLev k 1 r' (Hpk k r') := by
  have h := hCL k r' (Hpk k r') (hpk_mem k r') (y, s)
  rw [lev_inv] at h
  dsimp only at h
  rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, lev_sq, Matrix.one_mul, Matrix.mul_assoc, lev_sq,
    Matrix.mul_one]

def tm (k r' : ℕ) (x : HPar k r') : HPar k r' := (Hpk k r' *ᵥ (-x.1), -x.2)

theorem ga_yx (hCL : HeisConjLev) (hInv : HeisInv) (k r' : ℕ) (x : HPar k r') (l : Fin (1 + r' + 1)) :
    Ga k (1 + r') l (Yx k r' x) = Del k (1 + r') l (heis0 k r' (tm k r' x)) ^ 2 := by
  have hY : ∀ a, Yx k r' x a =
      ιLev k 1 r' (Hpk k r') *ᵥ (heis0 k r' (tm k r' x) *ᵥ phiV k (1 + r') a) := by
    intro a
    unfold Yx phi2 tm
    rw [hInv k r' x, heis_eq hCL k r' (-x.1) (-x.2), mv3 _ _ (lev_sq k r')]
  have hY' : Yx k r' x = fun a =>
      ιLev k 1 r' (Hpk k r') *ᵥ (heis0 k r' (tm k r' x) *ᵥ phiV k (1 + r') a) := funext hY
  have hU : (ιLev k 1 r' (Hpk k r'))ᴴ * ιLev k 1 r' (Hpk k r') = 1 := by rw [lev_conjT, lev_sq]
  rw [hY', ga_unit k (1 + r') l hU]
  unfold Del
  rw [Real.sq_sqrt (ga_nn _ _ _ _)]

theorem sgn_mp (k r' : ℕ) (i : Fin (2 * r' + k + 1)) :
    MeasurePreserving (fun z : ℂ => (-GS.sgnI k r' i) * z) volume volume := by
  unfold GS.sgnI
  split_ifs
  · simp only [neg_neg, one_mul]
    exact MeasurePreserving.id volume
  · simp only [neg_mul, one_mul]
    exact Measure.measurePreserving_neg volume

theorem hpk_neg_mp (k r' : ℕ) :
    MeasurePreserving (fun v : Fin (2 * r' + k + 1) → ℂ => Hpk k r' *ᵥ (-v)) volume volume := by
  have hP := volume_preserving_arrowCongr' (GS.sigE k r') (MeasurableEquiv.refl ℂ)
    (MeasurePreserving.id volume)
  have hS := volume_preserving_pi (f := fun (i : Fin (2 * r' + k + 1)) (z : ℂ) => (-GS.sgnI k r' i) * z)
    fun i => sgn_mp k r' i
  have e : (fun v : Fin (2 * r' + k + 1) → ℂ => Hpk k r' *ᵥ (-v)) =
      (fun (v : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) => (-GS.sgnI k r' i) * v i) ∘
        MeasurableEquiv.arrowCongr' (GS.sigE k r') (MeasurableEquiv.refl ℂ) := by
    funext v i
    simp only [Function.comp_apply, Pi.neg_apply, GS.hpk_mulVec, neg_mul, mul_neg]
    rfl
  rw [e]
  exact hS.comp hP

theorem tm_mp (k r' : ℕ) : MeasurePreserving (tm k r') volume volume :=
  (hpk_neg_mp k r').prod (Measure.measurePreserving_neg volume)

theorem lsq_cont {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => Lsq x l := by
  unfold Lsq
  exact continuous_const.add (continuous_finset_sum _ fun j _ => Continuous.if_const _
    (((continuous_apply j).comp continuous_fst).norm.pow 2) continuous_const)

theorem de_cont {p m : ℕ} (l : Fin (p + 1)) : Continuous fun x : Xp p m => de x l := by
  unfold de
  refine Real.continuous_sqrt.comp (((lsq_cont l).mul ?_).add ?_)
  · unfold rhoSq
    exact ((lsq_cont _).add (continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2)).add
      (continuous_finset_sum _ fun j _ => Continuous.if_const _
        (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm.pow 2) continuous_const)
  · have h2 : Continuous fun x : Xp p m => ∑ j : Fin p, if (l : ℕ) ≤ (j : ℕ) then x.2.1 j * star (x.1 j) else 0 :=
      continuous_finset_sum _ fun j _ => Continuous.if_const _
        (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
          ((continuous_apply j).comp continuous_fst).star) continuous_const
    unfold bco
    fun_prop

def chF (p m : ℕ) (ν : Fin (p + 1) → ℝ) (y : Xp p m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de y l ^ (-(s0N p m l + ν l)))

theorem chF_meas (p m : ℕ) (ν : Fin (p + 1) → ℝ) : Measurable (chF p m ν) := by
  unfold chF
  exact Finset.measurable_prod _ fun l _ => ENNReal.measurable_ofReal.comp ((de_cont l).measurable.pow_const _)

end ThFin

theorem th_fin (hB2 : InductiveHeisenbergInputs) (hF : FormulaF) (hCH : CH) (k r' : ℕ) (hk : 1 ≤ k) (t : Fin (1 + r' + 1) → ℝ)
    (hν : CHCond (1 + r') fun l => t l - s0N (1 + r') (k - 1) l) :
    (∫⁻ x : HPar k r', ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^ (-t l / 2))) < ∞ := by
  obtain ⟨-, -, -, -, -, hCL, -, hInv, -⟩ := hB2
  obtain ⟨hF1, hF2⟩ := hF k r' hk
  have hpt : ∀ x : HPar k r', (∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^ (-t l / 2))) =
      ThFin.chF (1 + r') (k - 1) (fun l => t l - s0N (1 + r') (k - 1) l)
        (hcoord k r' (ThFin.tm k r' x)) := by
    intro x
    unfold ThFin.chF
    refine Finset.prod_congr rfl fun l _ => ?_
    have hd : 0 ≤ de (hcoord k r' (ThFin.tm k r' x)) l := Real.sqrt_nonneg _
    have he : ((2 : ℕ) : ℝ) * (-t l / 2) =
        -(s0N (1 + r') (k - 1) l + (t l - s0N (1 + r') (k - 1) l)) := by
      push_cast; ring
    rw [ThFin.ga_yx hCL hInv k r' x l, hF1, ← Real.rpow_natCast, ← Real.rpow_mul hd, he]
  calc (∫⁻ x : HPar k r', ∏ l, ENNReal.ofReal (Ga k (1 + r') l (Yx k r' x) ^ (-t l / 2)))
      = ∫⁻ x : HPar k r', ThFin.chF (1 + r') (k - 1) (fun l => t l - s0N (1 + r') (k - 1) l)
          (hcoord k r' (ThFin.tm k r' x)) := lintegral_congr hpt
    _ = ∫⁻ y, ThFin.chF (1 + r') (k - 1) (fun l => t l - s0N (1 + r') (k - 1) l) y :=
        (hF2.comp (ThFin.tm_mp k r')).lintegral_comp (ThFin.chF_meas _ _ _)
    _ < ∞ := hCH (1 + r') (k - 1) _ hν

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA

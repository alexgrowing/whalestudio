import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LinIndToLp

noncomputable section

open Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.DetB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem entry_le_gN {k r : ℕ} (h : Mat k r) (m j : Fin (2 * r + k + 1)) : ‖h m j‖ ≤ gN h := by
  unfold gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (h m j) ≤ ∑ j', Complex.normSq (h m j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (h m j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j', Complex.normSq (h i j') :=
        Finset.single_le_sum (f := fun i => ∑ j', Complex.normSq (h i j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ m)

def cst {k r : ℕ} (H : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  ∑ i, ∑ m, ∑ j, ‖w i‖ * ‖H i m‖ * ‖v j‖

theorem cst_nonneg {k r : ℕ} (H : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) : 0 ≤ cst H v w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem herm_le {k r : ℕ} (H h : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    ‖herm H (h *ᵥ v) w‖ ≤ cst H v w * gN h := by
  have hb := entry_le_gN h
  unfold herm cst
  calc ‖star w ⬝ᵥ (H *ᵥ (h *ᵥ v))‖ = ‖∑ i, ∑ m, ∑ j, star (w i) * (H i m * (h m j * v j))‖ := by
        simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    _ ≤ ∑ i, ∑ m, ∑ j, ‖star (w i) * (H i m * (h m j * v j))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun m _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ m, ∑ j, ‖w i‖ * ‖H i m‖ * ‖v j‖ * gN h := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_mul, norm_mul, norm_star]
        calc ‖w i‖ * (‖H i m‖ * (‖h m j‖ * ‖v j‖)) = (‖w i‖ * ‖H i m‖ * ‖v j‖) * ‖h m j‖ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hb m j) (by positivity)
    _ = (∑ i, ∑ m, ∑ j, ‖w i‖ * ‖H i m‖ * ‖v j‖) * gN h := by simp only [Finset.sum_mul]

def K0 (k r : ℕ) : ℝ := ∑ a : Fin (r + 1), ∑ b : Fin (r + 1), cst (Hpk k r) (phiV' k r b) (phiV' k r a)

theorem lipschitzConst_nonneg (k r : ℕ) : 0 ≤ K0 k r :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => cst_nonneg _ _ _

theorem hermForm_phi_le_bound (k r : ℕ) (a b : Fin (r + 1)) :
    cst (Hpk k r) (phiV' k r b) (phiV' k r a) ≤ K0 k r := by
  unfold K0
  calc cst (Hpk k r) (phiV' k r b) (phiV' k r a) ≤ ∑ b', cst (Hpk k r) (phiV' k r b') (phiV' k r a) :=
        Finset.single_le_sum (f := fun b' => cst (Hpk k r) (phiV' k r b') (phiV' k r a))
          (fun _ _ => cst_nonneg _ _ _) (Finset.mem_univ b)
    _ ≤ _ := Finset.single_le_sum (f := fun a' => ∑ b', cst (Hpk k r) (phiV' k r b') (phiV' k r a'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => cst_nonneg _ _ _) (Finset.mem_univ a)

theorem Dl_le (k r : ℕ) (l : Fin (r + 1)) (h : Mat k r) :
    ‖Dl k r l h‖ ≤ (l.val + 1).factorial * (K0 k r * gN h) ^ (l.val + 1) := by
  have hx : ∀ i j, NormedField.toAbsoluteValue ℂ ((Matrix.of fun a b : Fin (l.val + 1) =>
      herm (Hpk k r) (h *ᵥ phiV' k r (Fin.castLE (by omega) b)) (phiV' k r (Fin.castLE (by omega) a))) i j)
        ≤ K0 k r * gN h := by
    intro i j
    show ‖herm (Hpk k r) (h *ᵥ phiV' k r _) (phiV' k r _)‖ ≤ _
    exact (herm_le _ _ _ _).trans (mul_le_mul_of_nonneg_right (hermForm_phi_le_bound _ _ _ _)
      (le_trans (norm_nonneg _) (entry_le_gN h 0 0)))
  have := Matrix.det_le hx
  simp only [Fintype.card_fin, nsmul_eq_mul] at this
  exact this

def cl (k r : ℕ) (l : Fin (r + 1)) : ℝ := (l.val + 1).factorial * K0 k r ^ (l.val + 1) + 1

theorem cl_pos (k r : ℕ) (l : Fin (r + 1)) : 0 < cl k r l := by
  have := lipschitzConst_nonneg k r
  unfold cl; positivity

theorem fac_le (k r : ℕ) (l : Fin (r + 1)) (s : ℝ) (hs : 0 ≤ s) (h : Mat k r) (hM : 1 ≤ gN h) :
    ENNReal.ofReal (gN h ^ (-(((l.val : ℝ) + 1) * s))) ≤
      ENNReal.ofReal (cl k r l ^ s) * (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s) := by
  have hM0 : 0 < gN h := by linarith
  have hc := cl_pos k r l
  have hK := lipschitzConst_nonneg k r
  have hD : ‖Dl k r l h‖ ≤ cl k r l * gN h ^ (l.val + 1) := by
    have := Dl_le k r l h
    rw [mul_pow, ← mul_assoc] at this
    refine this.trans ?_
    unfold cl
    have : 0 ≤ gN h ^ (l.val + 1) := by positivity
    nlinarith
  have hb : 0 < cl k r l * gN h ^ (l.val + 1) := mul_pos hc (pow_pos hM0 _)
  have h1 : (‖Dl k r l h‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (cl k r l * gN h ^ (l.val + 1)) := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]; exact ENNReal.ofReal_le_ofReal hD
  have h2 : ENNReal.ofReal (cl k r l * gN h ^ (l.val + 1)) ^ (-s) ≤ (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow h1 hs)
  refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl h2)
  rw [ENNReal.ofReal_rpow_of_pos hb, ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
  congr 1
  rw [Real.mul_rpow hc.le (pow_nonneg hM0.le _), Real.rpow_neg hc.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hM0.le, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hc s).ne', one_mul]
  congr 1
  push_cast; ring

end ReciprocityTheory.ChartRestriction.DS.Xi.DetB

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 DetB

theorem detH (hB2 : InductiveHeisenbergInputs) : DET := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGN, -⟩ := hB2
  intro k r s A _ hs hA
  refine ⟨∏ l, Real.toNNReal (cl k r l ^ s l), fun h hh => ?_⟩
  have hM : 1 ≤ gN h := hGN k r h hh
  have hM0 : 0 < gN h := by linarith
  calc ENNReal.ofReal (gN h ^ (-A))
        ≤ ENNReal.ofReal (gN h ^ (-∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l)) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hM (neg_le_neg hA))
    _ = ∏ l : Fin (r + 1), ENNReal.ofReal (gN h ^ (-(((l.val : ℝ) + 1) * s l))) := by
        rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hM0,
          ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg hM0.le _)]
    _ ≤ ∏ l : Fin (r + 1), (ENNReal.ofReal (cl k r l ^ s l) * (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s l)) :=
        Finset.prod_le_prod' fun l _ => fac_le k r l (s l) (hs l) h hM
    _ = _ := by
        rw [Finset.prod_mul_distrib, FsE, ENNReal.ofNNReal_finsetProd]; rfl

end ReciprocityTheory.ChartRestriction.DS.Xi

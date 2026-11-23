import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta

open Matrix MeasureTheory
open scoped ComplexConjugate

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG.RP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBH

variable {k ρ : ℕ}

theorem nq_L (y : U.RC k 1 ρ) (Q : B.Mat k (1 + ρ)) (q : Fin (2 * (1 + ρ) + k + 1)) :
    (U.Rn k 1 ρ y * Q) (U.eB k 1 ρ (Sum.inr 0)) q = Q (U.eB k 1 ρ (Sum.inr 0)) q := by
  rw [Matrix.mul_apply, ← (U.eB k 1 ρ).sum_comp]
  simp [U.Rn, U.blk3, Fintype.sum_sum_type]

theorem nq_V (y : U.RC k 1 ρ) (Q : B.Mat k (1 + ρ)) (w : Fin (2 * ρ + k + 1)) (q : Fin (2 * (1 + ρ) + k + 1)) :
    (U.Rn k 1 ρ y * Q) (U.eB k 1 ρ (Sum.inl (Sum.inr w))) q =
      Q (U.eB k 1 ρ (Sum.inl (Sum.inr w))) q + cy y w * Q (U.eB k 1 ρ (Sum.inr 0)) q := by
  rw [Matrix.mul_apply, ← (U.eB k 1 ρ).sum_comp]
  simp [U.Rn, U.blk3, Fintype.sum_sum_type, Matrix.one_apply, cy]

private theorem wMat_one_eq_one : G.wMat 1 = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [G.wMat]

theorem nq_0 (y : U.RC k 1 ρ) (Q : B.Mat k (1 + ρ)) (q : Fin (2 * (1 + ρ) + k + 1)) :
    (U.Rn k 1 ρ y * Q) (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) q =
      Q (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) q +
        ∑ v, -Matrix.vecMul (star (cy y)) (Hpk k ρ) v * Q (U.eB k 1 ρ (Sum.inl (Sum.inr v))) q +
        (-(1 / 2 : ℂ) * nn y + Complex.I * (dy y : ℂ)) * Q (U.eB k 1 ρ (Sum.inr 0)) q := by
  rw [Matrix.mul_apply, ← (U.eB k 1 ρ).sum_comp]
  simp [U.Rn, U.blk3, Fintype.sum_sum_type, wMat_one_eq_one, cy, dy, nn, U.skewOf, G.strictUpper,
    Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]

theorem mn_L (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) (N : B.Mat k (1 + ρ)) (q : Fin (2 * (1 + ρ) + k + 1)) :
    (U.mMap k 1 ρ Z γ * N) (U.eB k 1 ρ (Sum.inr 0)) q = Z 0 0 * N (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) q := by
  rw [Matrix.mul_apply, ← (U.eB k 1 ρ).sum_comp]
  simp [U.mMap, U.blk3, Fintype.sum_sum_type, wMat_one_eq_one]

theorem mn_V (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) (N : B.Mat k (1 + ρ)) (w : Fin (2 * ρ + k + 1))
    (q : Fin (2 * (1 + ρ) + k + 1)) :
    (U.mMap k 1 ρ Z γ * N) (U.eB k 1 ρ (Sum.inl (Sum.inr w))) q =
      ∑ v, γ w v * N (U.eB k 1 ρ (Sum.inl (Sum.inr v))) q := by
  rw [Matrix.mul_apply, ← (U.eB k 1 ρ).sum_comp]
  simp [U.mMap, U.blk3, Fintype.sum_sum_type]

theorem mn_0 (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) (N : B.Mat k (1 + ρ)) (q : Fin (2 * (1 + ρ) + k + 1)) :
    (U.mMap k 1 ρ Z γ * N) (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) q =
      (Zᴴ⁻¹ * G.wMat 1) 0 0 * N (U.eB k 1 ρ (Sum.inr 0)) q := by
  rw [Matrix.mul_apply, ← (U.eB k 1 ρ).sum_comp]
  simp [U.mMap, U.blk3, Fintype.sum_sum_type]

theorem radial_entry_middle_zero (y : U.RC k 1 ρ) (v : Fin (2 * ρ + k + 1)) :
    U.Rn k 1 ρ y (U.eB k 1 ρ (Sum.inl (Sum.inr v))) (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) = 0 := by
  simp [radical_unipotent_rank_one_apply]

theorem rn_VV (y : U.RC k 1 ρ) (v u : Fin (2 * ρ + k + 1)) :
    U.Rn k 1 ρ y (U.eB k 1 ρ (Sum.inl (Sum.inr v))) (U.eB k 1 ρ (Sum.inl (Sum.inr u))) = if v = u then 1 else 0 := by
  simp [radical_unipotent_rank_one_apply, Matrix.one_apply]

theorem radial_entry_lower_zero (y : U.RC k 1 ρ) :
    U.Rn k 1 ρ y (U.eB k 1 ρ (Sum.inr 0)) (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) = 0 := by
  simp [radical_unipotent_rank_one_apply]

theorem hpk_le (a b : Fin (2 * ρ + k + 1)) : ‖Hpk k ρ a b‖ ≤ 1 := by
  unfold Hpk; split_ifs <;> simp

theorem hpk_sq : Hpk k ρ * Hpk k ρ = 1 := Formalism.FourierDecayAlt.P.Qx2.hpk_sq'

theorem vm_bd {N : ℕ} (s : Fin N → ℂ) (H : Matrix (Fin N) (Fin N) ℂ) (hH : ∀ i j, ‖H i j‖ ≤ 1) {A : ℝ}
    (hA : 0 ≤ A) (hs : ∀ i, ‖s i‖ ≤ A) (v : Fin N) : ‖Matrix.vecMul s H v‖ ≤ N * A := by
  rw [Matrix.vecMul]
  unfold dotProduct
  calc ‖∑ i, s i * H i v‖ ≤ ∑ i, ‖s i * H i v‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, A := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        calc ‖s i‖ * ‖H i v‖ ≤ A * 1 := mul_le_mul (hs i) (hH i v) (norm_nonneg _) hA
          _ = A := mul_one A
    _ = N * A := by simp

theorem dot_bd {N : ℕ} (u w : Fin N → ℂ) {A B' : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B') (hu : ∀ i, ‖u i‖ ≤ A)
    (hw : ∀ i, ‖w i‖ ≤ B') : ‖u ⬝ᵥ w‖ ≤ N * (A * B') := by
  unfold dotProduct
  calc ‖∑ i, u i * w i‖ ≤ ∑ i, ‖u i * w i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin N, A * B' := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul]
        exact mul_le_mul (hu i) (hw i) (norm_nonneg _) hA
    _ = N * (A * B') := by simp

theorem div_bd {a t : ℂ} {B' δ : ℝ} (hδ : 0 < δ) (ht : δ ≤ ‖t‖) (h : ‖a * t‖ ≤ B') : ‖a‖ ≤ B' / δ := by
  rw [norm_mul] at h
  rw [le_div_iff₀ hδ]
  calc ‖a‖ * δ ≤ ‖a‖ * ‖t‖ := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
    _ ≤ B' := h

theorem norm_Id (d : ℝ) : ‖Complex.I * (d : ℂ)‖ = |d| := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem rc_bd (x : U.RC k 1 ρ) {M : ℝ} (hM : 0 ≤ M) (hc : ∀ v, ‖cy x v‖ ≤ M) (hd : |dy x| ≤ M) : ‖x‖ ≤ M := by
  have h1 : ‖x.1‖ ≤ M := by
    refine (pi_norm_le_iff_of_nonneg hM).2 fun v => (pi_norm_le_iff_of_nonneg hM).2 fun i => ?_
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact hc v
  have h2 : ‖x.2.1‖ ≤ M := by
    refine (pi_norm_le_iff_of_nonneg hM).2 fun p => ?_
    exact absurd p.2 (by have := p.1.1.2; have := p.1.2.2; omega)
  have h3 : ‖x.2.2‖ ≤ M := by
    refine (pi_norm_le_iff_of_nonneg hM).2 fun i => ?_
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [Real.norm_eq_abs]
    exact hd
  rw [Prod.norm_def, Prod.norm_def]
  exact max_le h1 (max_le h2 h3)

private theorem rn_eB_zero_entries_eq (y : U.RC k 1 ρ) :
    U.Rn k 1 ρ y (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) = 1 ∧
      (∀ v, U.Rn k 1 ρ y (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) (U.eB k 1 ρ (Sum.inl (Sum.inr v))) =
        -Matrix.vecMul (star (cy y)) (Hpk k ρ) v) ∧
      U.Rn k 1 ρ y (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) (U.eB k 1 ρ (Sum.inr 0)) =
        -(1 / 2 : ℂ) * nn y + Complex.I * (dy y : ℂ) := by
  refine ⟨?_, fun v => ?_, ?_⟩ <;>
    simp [U.Rn, U.blk3, wMat_one_eq_one, cy, dy, nn, U.skewOf, G.strictUpper, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]

theorem rad_main (t : ℂ) (γ : B.Mat k ρ) (x x' : U.RC k 1 ρ) {R δ : ℝ} (hδ : 0 < δ) (hR0 : 0 ≤ R)
    (ht : δ ≤ ‖t‖)
    (hQ : ∀ p q, ‖((U.Rn k 1 ρ x)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ * U.Rn k 1 ρ x') p q‖ ≤ R) :
    (∀ v, ‖cy x v‖ ≤ R / δ) ∧
      |dy x| ≤ R / δ + ((2 * ρ + k + 1 : ℕ) : ℝ) * ((((2 * ρ + k + 1 : ℕ) : ℝ) * (R / δ)) * (R / δ)) / 2 ∧
      (∀ v, ‖cy x' v‖ ≤ ((2 * ρ + k + 1 : ℕ) : ℝ) * (R / δ)) ∧
      |dy x'| ≤ R / δ + ((2 * ρ + k + 1 : ℕ) : ℝ) * ((R / δ) * (((2 * ρ + k + 1 : ℕ) : ℝ) * (R / δ))) / 2 ∧
      ∀ i j, ‖γ i j‖ ≤ R + R / δ * R := by
  have hRd : 0 ≤ R / δ := div_nonneg hR0 hδ.le
  have hnR : 0 ≤ ((2 * ρ + k + 1 : ℕ) : ℝ) * (R / δ) := mul_nonneg (Nat.cast_nonneg _) hRd
  set P := (U.Rn k 1 ρ x)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ * U.Rn k 1 ρ x' with hPdef
  have key : U.Rn k 1 ρ x * P = U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ * U.Rn k 1 ρ x' := by
    rw [hPdef, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ (rn_unit x), one_mul]
  have eL : ∀ q, P (U.eB k 1 ρ (Sum.inr 0)) q = t * U.Rn k 1 ρ x' (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) q := by
    intro q
    have h := congrFun (congrFun key (U.eB k 1 ρ (Sum.inr 0))) q
    rw [nq_L, mn_L] at h
    simpa using h
  have eV : ∀ w q, P (U.eB k 1 ρ (Sum.inl (Sum.inr w))) q + cy x w * P (U.eB k 1 ρ (Sum.inr 0)) q =
      ∑ v, γ w v * U.Rn k 1 ρ x' (U.eB k 1 ρ (Sum.inl (Sum.inr v))) q := by
    intro w q
    have h := congrFun (congrFun key (U.eB k 1 ρ (Sum.inl (Sum.inr w)))) q
    rw [nq_V, mn_V] at h
    exact h
  have eO := congrFun (congrFun key (U.eB k 1 ρ (Sum.inl (Sum.inl 0)))) (U.eB k 1 ρ (Sum.inl (Sum.inl 0)))
  rw [nq_0, mn_0, radial_entry_lower_zero, mul_zero] at eO
  obtain ⟨hOO, hOV, hOL⟩ := rn_eB_zero_entries_eq x'
  have PLO : P (U.eB k 1 ρ (Sum.inr 0)) (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) = t := by
    rw [eL, hOO, mul_one]
  have PVO : ∀ w, P (U.eB k 1 ρ (Sum.inl (Sum.inr w))) (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) = -(cy x w * t) := by
    intro w
    have h := eV w (U.eB k 1 ρ (Sum.inl (Sum.inl 0)))
    rw [PLO, Finset.sum_eq_zero (fun v _ => by rw [radial_entry_middle_zero, mul_zero])] at h
    linear_combination h
  have hcx : ∀ v, ‖cy x v‖ ≤ R / δ := fun v =>
    div_bd hδ ht (by rw [← norm_neg, ← PVO]; exact hQ _ _)
  have hux : ∀ v, ‖Matrix.vecMul (star (cy x)) (Hpk k ρ) v‖ ≤ ((2 * ρ + k + 1 : ℕ) : ℝ) * (R / δ) :=
    vm_bd _ _ hpk_le hRd (fun i => by rw [Pi.star_apply, norm_star]; exact hcx i)
  have hnn : ‖nn x‖ ≤ ((2 * ρ + k + 1 : ℕ) : ℝ) * ((((2 * ρ + k + 1 : ℕ) : ℝ) * (R / δ)) * (R / δ)) :=
    dot_bd _ _ hnR hRd hux hcx
  rw [PLO] at eO
  simp only [PVO] at eO
  have hsum : ∑ v, -Matrix.vecMul (star (cy x)) (Hpk k ρ) v * -(cy x v * t) = nn x * t := by
    unfold nn dotProduct
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [hsum] at eO
  have ha : ‖(1 / 2 : ℂ) * nn x + Complex.I * (dy x : ℂ)‖ ≤ R / δ := by
    refine div_bd hδ ht ?_
    have h : ((1 / 2 : ℂ) * nn x + Complex.I * (dy x : ℂ)) * t =
        -P (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) (U.eB k 1 ρ (Sum.inl (Sum.inl 0))) := by
      linear_combination eO
    rw [h, norm_neg]
    exact hQ _ _
  have PLV : ∀ v, P (U.eB k 1 ρ (Sum.inr 0)) (U.eB k 1 ρ (Sum.inl (Sum.inr v))) =
      t * -Matrix.vecMul (star (cy x')) (Hpk k ρ) v := by
    intro v
    rw [eL, hOV]
  have hu' : ∀ v, ‖Matrix.vecMul (star (cy x')) (Hpk k ρ) v‖ ≤ R / δ := by
    intro v
    refine div_bd hδ ht ?_
    calc ‖Matrix.vecMul (star (cy x')) (Hpk k ρ) v * t‖
        = ‖P (U.eB k 1 ρ (Sum.inr 0)) (U.eB k 1 ρ (Sum.inl (Sum.inr v)))‖ := by
          rw [PLV, norm_mul, norm_mul, norm_neg, mul_comm]
      _ ≤ R := hQ _ _
  have hs : Matrix.vecMul (Matrix.vecMul (star (cy x')) (Hpk k ρ)) (Hpk k ρ) = star (cy x') := by
    rw [Matrix.vecMul_vecMul, hpk_sq, Matrix.vecMul_one]
  have hcx' : ∀ v, ‖cy x' v‖ ≤ ((2 * ρ + k + 1 : ℕ) : ℝ) * (R / δ) := by
    intro v
    rw [← norm_star, ← Pi.star_apply, ← hs]
    exact vm_bd _ _ hpk_le hRd hu' v
  have hnn' : ‖nn x'‖ ≤ ((2 * ρ + k + 1 : ℕ) : ℝ) * ((R / δ) * (((2 * ρ + k + 1 : ℕ) : ℝ) * (R / δ))) :=
    dot_bd _ _ hRd hnR hu' hcx'
  have ha' : ‖-(1 / 2 : ℂ) * nn x' + Complex.I * (dy x' : ℂ)‖ ≤ R / δ := by
    refine div_bd hδ ht ?_
    rw [mul_comm, ← hOL, ← eL]
    exact hQ _ _
  have hhalf : ∀ z : ℂ, ‖(1 / 2 : ℂ) * z‖ = ‖z‖ / 2 := by
    intro z
    rw [norm_mul]
    norm_num
    ring
  refine ⟨hcx, ?_, hcx', ?_, ?_⟩
  · calc |dy x| = ‖Complex.I * (dy x : ℂ)‖ := (norm_Id _).symm
      _ = ‖((1 / 2 : ℂ) * nn x + Complex.I * (dy x : ℂ)) - (1 / 2 : ℂ) * nn x‖ := by ring_nf
      _ ≤ ‖(1 / 2 : ℂ) * nn x + Complex.I * (dy x : ℂ)‖ + ‖(1 / 2 : ℂ) * nn x‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [hhalf]
        linarith
  · calc |dy x'| = ‖Complex.I * (dy x' : ℂ)‖ := (norm_Id _).symm
      _ = ‖(-(1 / 2 : ℂ) * nn x' + Complex.I * (dy x' : ℂ)) + (1 / 2 : ℂ) * nn x'‖ := by ring_nf
      _ ≤ ‖-(1 / 2 : ℂ) * nn x' + Complex.I * (dy x' : ℂ)‖ + ‖(1 / 2 : ℂ) * nn x'‖ := norm_add_le _ _
      _ ≤ _ := by
        rw [hhalf]
        linarith
  · intro i j
    have h := eV i (U.eB k 1 ρ (Sum.inl (Sum.inr j)))
    simp only [rn_VV, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [← h]
    calc _ ≤ ‖P (U.eB k 1 ρ (Sum.inl (Sum.inr i))) (U.eB k 1 ρ (Sum.inl (Sum.inr j)))‖ +
          ‖cy x i * P (U.eB k 1 ρ (Sum.inr 0)) (U.eB k 1 ρ (Sum.inl (Sum.inr j)))‖ := norm_add_le _ _
      _ ≤ R + R / δ * R := by
        rw [norm_mul]
        gcongr
        · exact hQ _ _
        · exact hcx i
        · exact hQ _ _

end Formalism.FourierDecayAlt.P.CutSH.SFG.RP

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.CutSH.SFG.RP

theorem radial_proper : RadProper := by
  intro k ρ m e δ R hδ
  set R0 := max R 0 with hR0def
  have hR0 : 0 ≤ R0 := le_max_right _ _
  have hb : 0 ≤ R0 / δ := div_nonneg hR0 hδ.le
  have hn : (0 : ℝ) ≤ ((2 * ρ + k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnb : 0 ≤ ((2 * ρ + k + 1 : ℕ) : ℝ) * (R0 / δ) := mul_nonneg hn hb
  set Mx := R0 / δ + ((2 * ρ + k + 1 : ℕ) : ℝ) * ((((2 * ρ + k + 1 : ℕ) : ℝ) * (R0 / δ)) * (R0 / δ)) / 2
    with hMx
  set Mx' := ((2 * ρ + k + 1 : ℕ) : ℝ) * (R0 / δ) +
    (R0 / δ + ((2 * ρ + k + 1 : ℕ) : ℝ) * ((R0 / δ) * (((2 * ρ + k + 1 : ℕ) : ℝ) * (R0 / δ))) / 2) with hMx'
  have h1 : 0 ≤ ((2 * ρ + k + 1 : ℕ) : ℝ) * ((((2 * ρ + k + 1 : ℕ) : ℝ) * (R0 / δ)) * (R0 / δ)) / 2 :=
    div_nonneg (mul_nonneg hn (mul_nonneg hnb hb)) (by norm_num)
  have h2 : 0 ≤ R0 / δ + ((2 * ρ + k + 1 : ℕ) : ℝ) * ((R0 / δ) * (((2 * ρ + k + 1 : ℕ) : ℝ) * (R0 / δ))) / 2 :=
    add_nonneg hb (div_nonneg (mul_nonneg hn (mul_nonneg hb hnb)) (by norm_num))
  have hMx0 : 0 ≤ Mx := add_nonneg hb h1
  have hMx'0 : 0 ≤ Mx' := add_nonneg hnb h2
  refine ⟨Metric.closedBall (0 : U.RC k 1 ρ) Mx ×ˢ Metric.closedBall (0 : U.RC k 1 ρ) Mx',
    {γ | ∀ i j, ‖γ i j‖ ≤ R0 + R0 / δ * R0}, ?_, ?_, ?_⟩
  · exact (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  · have hc := isCompact_univ_pi fun _ : Fin (2 * ρ + k + 1) =>
      isCompact_univ_pi fun _ : Fin (2 * ρ + k + 1) => isCompact_closedBall (0 : ℂ) (R0 + R0 / δ * R0)
    simp only [Set.pi, Set.mem_univ, forall_const, Metric.mem_closedBall, dist_zero_right] at hc
    exact hc
  · intro t γ xx ht hg
    have entry : ∀ p q : Fin (2 * (1 + ρ) + k + 1),
        ((U.Rn k 1 ρ xx.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ * U.Rn k 1 ρ xx.2) p q =
          pt e t γ xx (finCongr (by omega) p) (finCongr (by omega) q) := by
      intro p q
      subst e
      simp [pt, rn1, mc, D.castM, Matrix.reindex_apply, Matrix.inv_submatrix_equiv,
        Matrix.submatrix_mul_equiv]
    have gbd : ∀ i j, ‖pt e t γ xx i j‖ ≤ B.gN (pt e t γ xx) := by
      intro i j
      rw [Complex.norm_def]
      unfold B.gN
      apply Real.sqrt_le_sqrt
      calc Complex.normSq (pt e t γ xx i j) ≤ ∑ j', Complex.normSq (pt e t γ xx i j') :=
            Finset.single_le_sum (f := fun j' => Complex.normSq (pt e t γ xx i j'))
              (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
        _ ≤ ∑ i', ∑ j', Complex.normSq (pt e t γ xx i' j') :=
            Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (pt e t γ xx i' j'))
              (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    have hQ : ∀ p q, ‖((U.Rn k 1 ρ xx.1)⁻¹ * U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ * U.Rn k 1 ρ xx.2) p q‖ ≤ R0 := by
      intro p q
      rw [entry]
      exact (gbd _ _).trans (hg.trans (le_max_left _ _))
    obtain ⟨hc1, hd1, hc2, hd2, hγ⟩ := rad_main t γ xx.1 xx.2 hδ hR0 ht hQ
    refine ⟨Set.mem_prod.2 ⟨?_, ?_⟩, hγ⟩
    · rw [mem_closedBall_zero_iff]
      exact rc_bd _ hMx0 (fun v => (hc1 v).trans (le_add_of_nonneg_right h1)) hd1
    · rw [mem_closedBall_zero_iff]
      exact rc_bd _ hMx'0 (fun v => (hc2 v).trans (le_add_of_nonneg_right h2))
        (hd2.trans (le_add_of_nonneg_left hnb))

end Formalism.FourierDecayAlt.P.CutSH.SFG

import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyDiagonal
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyInvariant
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyCocycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyDiagonalAlt

def diagEnergy {e : ℕ} (l : Fin (e + 1) → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (e + 1),
    chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) k

theorem diag_posDef {e : ℕ} {l : Fin (e + 1) → ℝ} (hl : ∀ j, 0 < l j) :
    (Matrix.diagonal fun j => (l j : ℂ)).PosDef :=
  Matrix.posDef_diagonal_iff.mpr fun j => by simpa using hl j

theorem diag_congr {e : ℕ} (s d : Fin (e + 1) → ℝ) :
    (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => (d j : ℂ)) *
        Matrix.diagonal (fun j => (s j : ℂ)) =
      Matrix.diagonal fun j => ((s j * d j * s j : ℝ) : ℂ) := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext j
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem diagEnergy_mul (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement)
    {e : ℕ} {l l' : Fin (e + 1) → ℝ} (hl : ∀ j, 0 < l j) (hl' : ∀ j, 0 < l' j) :
    diagEnergy (l * l') = diagEnergy l + diagEnergy l' := by
  have hll' : ∀ j, 0 < (l * l') j := fun j => mul_pos (hl j) (hl' j)
  set s : Fin (e + 1) → ℝ := fun j => (Real.sqrt (l' j))⁻¹ with hs
  have hss : ∀ j, s j * s j * l' j = 1 := fun j => by
    simp only [hs]
    rw [← mul_inv, Real.mul_self_sqrt (hl' j).le, inv_mul_cancel₀ (hl' j).ne']
  have hsd : (Matrix.diagonal fun j => (s j : ℂ)).det ≠ 0 := by
    rw [det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    have : (Real.sqrt (l' j)) ≠ 0 := (Real.sqrt_pos.mpr (hl' j)).ne'
    simpa [hs] using this
  have h1 : (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => ((l * l') j : ℂ)) *
      Matrix.diagonal (fun j => (s j : ℂ)) = Matrix.diagonal fun j => (l j : ℂ) := by
    rw [diag_congr]
    congr 1
    funext j
    congr 1
    simp only [Pi.mul_apply]
    linear_combination (l j) * hss j
  have h2 : (Matrix.diagonal fun j => (s j : ℂ))ᴴ * Matrix.diagonal (fun j => (l' j : ℂ)) *
      Matrix.diagonal (fun j => (s j : ℂ)) = 1 := by
    rw [diag_congr, ← diagonal_one]
    congr 1
    funext j
    rw [show s j * l' j * s j = 1 by linarith [hss j]]
    simp
  have hterm : ∀ k, chartMixedEnergy (Matrix.diagonal fun j => ((l * l') j : ℂ))
      (Matrix.diagonal fun j => (l' j : ℂ)) k = chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) 1 k := by
    intro k
    rw [← hI e _ _ _ (diag_posDef hll') (diag_posDef hl') hsd k, h1, h2]
  unfold diagEnergy
  rw [hC e _ (Matrix.diagonal fun j => (l' j : ℂ)) 1 (diag_posDef hll') (diag_posDef hl') PosDef.one,
    Finset.sum_congr rfl fun k _ => hterm k]

theorem diagEnergy_perm (hI : ChartEnergyLinearInvariant.Statement) {e : ℕ} {l : Fin (e + 1) → ℝ}
    (hl : ∀ j, 0 < l j) (σ : Equiv.Perm (Fin (e + 1))) : diagEnergy (l ∘ σ) = diagEnergy l := by
  set C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := σ.symm.toPEquiv.toMatrix with hCdef
  have hCH : Cᴴ = σ.toPEquiv.toMatrix := by
    ext i j
    rw [hCdef, conjTranspose_apply, PEquiv.toMatrix_apply, PEquiv.toMatrix_apply]
    simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.symm_apply_eq]
    by_cases h : σ i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hconj : ∀ A : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ, Cᴴ * A * C = A.submatrix σ σ := by
    intro A
    rw [hCH, PEquiv.toMatrix_toPEquiv_mul, hCdef, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
    rfl
  have hCd : C.det ≠ 0 := by
    rw [hCdef, show (σ.symm.toPEquiv.toMatrix : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      Equiv.Perm.permMatrix ℂ σ.symm from rfl, det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
  have hterm : ∀ k, chartMixedEnergy (Matrix.diagonal fun j => (l j : ℂ)) 1 k =
      chartMixedEnergy (Matrix.diagonal fun j => ((l ∘ σ) j : ℂ)) 1 k := by
    intro k
    rw [← hI e _ _ C (diag_posDef hl) PosDef.one hCd k, hconj, hconj, submatrix_diagonal_equiv,
      submatrix_one_equiv]
    rfl
  unfold diagEnergy
  exact (Finset.sum_congr rfl fun k _ => hterm k).symm

theorem cxHessian_add_const {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (κ : ℝ) :
    cxHessian (fun y => φ y + κ) = cxHessian φ := by
  have h : fderiv ℝ (fun y => φ y + κ) = fderiv ℝ φ := funext fun x => fderiv_add_const κ
  funext z
  unfold cxHessian
  simp only [h]
  rfl

theorem maDensity_congr {D : ℕ} (φ ψ : Fin D → (Fin D → ℂ) → ℝ) (h : ∀ j, cxHessian (φ j) = cxHessian (ψ j))
    (z : Fin D → ℂ) : maDensity φ z = maDensity ψ z := by
  unfold maDensity
  simp only [h]

theorem hermChartPot_const {e : ℕ} {c : ℝ} (hc : 0 < c) (y : Fin e → ℂ) :
    hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) y =
      hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y + 1 / 2 * Real.log c := by
  set v : Fin (e + 1) → ℂ := Fin.cons 1 y with hv
  have hv0 : v ≠ 0 := fun h => by
    have := congr_fun h 0
    simp [hv] at this
  have hx : 0 < (star v ⬝ᵥ ((1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) *ᵥ v)).re :=
    PosDef.one.re_dotProduct_pos hv0
  have hq : (star v ⬝ᵥ ((Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) *ᵥ v)).re =
      c * (star v ⬝ᵥ ((1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) *ᵥ v)).re := by
    rw [← smul_one_eq_diagonal, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  unfold hermChartPot
  rw [← hv, hq, Real.sqrt_mul hc.le, Real.log_mul (Real.sqrt_pos.mpr hc).ne' (Real.sqrt_pos.mpr hx).ne',
    Real.log_sqrt hc.le]
  ring

theorem diagEnergy_const {e : ℕ} {c : ℝ} (hc : 0 < c) :
    diagEnergy (fun _ : Fin (e + 1) => c) =
      (e + 1) * (1 / 2 * Real.log c) * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have hpot : hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) =
      fun y => hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) y + 1 / 2 * Real.log c :=
    funext (hermChartPot_const hc)
  have hk : ∀ k, chartMixedEnergy (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ)) 1 k =
      1 / 2 * Real.log c * chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
    intro k
    have hd : ∀ y, maDensity (fun j : Fin e => if (j : ℕ) < k then
        hermChartPot (Matrix.diagonal fun _ : Fin (e + 1) => (c : ℂ))
        else hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) y =
        maDensity (fun _ : Fin e => hermChartPot (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) y := by
      refine maDensity_congr _ _ fun j => ?_
      split_ifs
      · rw [hpot, cxHessian_add_const]
      · rfl
    unfold chartMixedEnergy chartMass
    simp_rw [hd]
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [hpot]
    ring
  unfold diagEnergy
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

theorem diagEnergy_one {e : ℕ} : diagEnergy (1 : Fin (e + 1) → ℝ) = 0 := by
  calc diagEnergy (1 : Fin (e + 1) → ℝ) = diagEnergy (fun _ : Fin (e + 1) => (1 : ℝ)) := rfl
    _ = 0 := by rw [diagEnergy_const one_pos, Real.log_one]; ring

theorem diagEnergy_prod (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement)
    {e : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Fin (e + 1) → ℝ) (hf : ∀ t j, 0 < f t j) :
    diagEnergy (∏ t ∈ s, f t) = ∑ t ∈ s, diagEnergy (f t) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact diagEnergy_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      diagEnergy_mul hI hC (hf a) (fun j => by rw [Finset.prod_apply]; exact Finset.prod_pos fun t _ => hf t j),
      ih]

end ChartEnergyDiagonalAlt

open ChartEnergyDiagonalAlt in

theorem ChartEnergyDiagonal.proof (hI : ChartEnergyLinearInvariant.Statement) (hC : ChartEnergyCocycle.Statement) :
    ChartEnergyDiagonal.Statement := by
  intro e l hl
  change diagEnergy l = _
  set f : Fin (e + 1) → Fin (e + 1) → ℝ := fun t => l ∘ (Equiv.addRight t) with hf
  have hfpos : ∀ t j, 0 < f t j := fun t j => hl _
  have hprod : (∏ t, f t) = fun _ => ∏ j, l j := by
    funext i
    rw [Finset.prod_apply]
    exact Equiv.prod_comp (Equiv.addLeft i) l
  have key := diagEnergy_prod hI hC Finset.univ f hfpos
  rw [hprod, diagEnergy_const (Finset.prod_pos fun j _ => hl j),
    Finset.sum_congr rfl fun t _ => diagEnergy_perm hI hl (Equiv.addRight t), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.log_prod (fun j _ => (hl j).ne')] at key
  push_cast at key
  have he : (0 : ℝ) < e + 1 := by positivity
  have h2 : ((e : ℝ) + 1) * (diagEnergy l - 1 / 2 * (∑ j, Real.log (l j)) *
      chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)) = 0 := by
    linear_combination -key
  have := (mul_eq_zero.mp h2).resolve_left he.ne'
  linarith

end

end GroundTheory.Heights₂.Heights

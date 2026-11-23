import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousOnPolarLog

noncomputable section
namespace GlobalTheory.CoshPowMeas
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
open Filter Topology

variable {p q : ℕ}

theorem continuous_cartanB : Continuous (cartanB : UpqT p q → Matrix (Fin p) (Fin q) ℂ) := by
  have h : Continuous fun g : UpqT p q => GlobalTheory.PolarLogCont.halfLog (UpqT.mat g) :=
    GlobalTheory.PolarLogCont.continuousOn_halfLog.comp_continuous GlobalTheory.UpqTopology.continuous_mat
      fun g => Units.isUnit (show Formalism.UG.Upq p q from g).1
  have hc : Continuous fun M : Mat p q => M.toBlocks₁₂ := by
    refine continuous_matrix fun i j => ?_
    exact continuous_id.matrix_elem (Sum.inl i) (Sum.inr j)
  exact hc.comp h

def sPad (B : Matrix (Fin p) (Fin q) ℂ) (j : Fin q) : ℝ := if (j : ℕ) < p then singVal B j else 0

theorem exists_gram (B : Matrix (Fin p) (Fin q) ℂ) : ∃ V : Matrix (Fin q) (Fin q) ℂ, Vᴴ * V = 1 ∧
    Bᴴ * B = V * Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2) * Vᴴ := by
  obtain ⟨U, hU, V, hV, hB⟩ := GlobalTheory.RectSVD.exists_svd_singularValues p q B
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have h2 : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  refine ⟨V, h2, ?_⟩
  set D : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0 with hD
  have hDD : Dᴴ * D = Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2) := by
    ext j j'
    rw [Matrix.mul_apply]
    by_cases hj : (j : ℕ) < p
    · rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin p)]
      · by_cases hjj : j = j'
        · subst hjj
          simp [hD, sPad, hj, singVal, sq]
        · have : (j : ℕ) ≠ j' := fun h => hjj (Fin.ext h)
          simp [hD, hjj, this]
      · intro i _ hi
        have : (i : ℕ) ≠ j := fun h => hi (Fin.ext h)
        simp [hD, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · by_cases hjj : j = j'
        · subst hjj
          simp [sPad, hj]
        · simp [hjj]
      · intro i _
        have : (i : ℕ) ≠ j := fun h => hj (h ▸ i.isLt)
        simp [hD, this]
  rw [← hDD]
  conv_lhs => rw [hB]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, h1, Matrix.one_mul]

theorem conj_pow {n : Type} [Fintype n] [DecidableEq n] (V A : Matrix n n ℂ) (h : Vᴴ * V = 1) (k : ℕ) :
    (V * A * Vᴴ) ^ k = V * A ^ k * Vᴴ := by
  induction k with
  | zero => simp [mul_eq_one_comm.1 h]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Vᴴ V, h, Matrix.one_mul]

def coshSum (n : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  ∑ k ∈ Finset.range n, (((2 * k).factorial : ℕ) : ℂ)⁻¹ • (Bᴴ * B) ^ k

theorem continuous_coshSum (n : ℕ) : Continuous (coshSum n : Matrix (Fin p) (Fin q) ℂ → _) := by
  unfold coshSum
  refine continuous_finset_sum _ fun k _ => ?_
  have h : Continuous fun B : Matrix (Fin p) (Fin q) ℂ => Bᴴ * B :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  exact (h.pow k).const_smul ((((2 * k).factorial : ℕ) : ℂ)⁻¹)

theorem det_coshSum (n : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) : (coshSum n B).det.re =
    ∏ j : Fin q, ∑ k ∈ Finset.range n, sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) := by
  obtain ⟨V, hV, h⟩ := exists_gram B
  have e : coshSum n B = V * Matrix.diagonal (fun j => ((∑ k ∈ Finset.range n,
      sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) : ℝ) : ℂ)) * Vᴴ := by
    have e1 : Matrix.diagonal (fun j => ((∑ k ∈ Finset.range n,
      sPad B j ^ (2 * k) / ((2 * k).factorial : ℕ) : ℝ) : ℂ)) = ∑ k ∈ Finset.range n,
        (((2 * k).factorial : ℕ) : ℂ)⁻¹ • (Matrix.diagonal (fun j => ((sPad B j : ℝ) : ℂ) ^ 2)) ^ k := by
      ext i j
      simp only [Matrix.diagonal_pow, Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply]
      split_ifs
      · push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [pow_mul, div_eq_inv_mul]
      · simp
    rw [e1, coshSum, h, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conj_pow _ _ hV, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.det_mul_comm, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.det_diagonal,
    ← Complex.ofReal_prod, Complex.ofReal_re]

theorem prod_cosh_sPad (B : Matrix (Fin p) (Fin q) ℂ) :
    ∏ j : Fin q, Real.cosh (sPad B j) = ∏ i ∈ Finset.range (min p q), Real.cosh (singVal B i) := by
  unfold sPad
  rw [Fin.prod_univ_eq_prod_range (fun j => Real.cosh (if j < p then singVal B j else 0)) q]
  symm
  refine Finset.prod_subset_one_on_sdiff (Finset.range_subset_range.2 (min_le_right p q)) ?_ ?_
  · intro x hx
    have : ¬ x < p := by
      simp only [Finset.mem_sdiff, Finset.mem_range] at hx; omega
    simp [this]
  · intro x hx
    have : x < p := by
      simp only [Finset.mem_range] at hx; omega
    simp [this]

theorem tendsto_det_coshSum (B : Matrix (Fin p) (Fin q) ℂ) :
    Tendsto (fun n => (coshSum n B).det.re) atTop
      (𝓝 (∏ i ∈ Finset.range (min p q), Real.cosh (singVal B i))) := by
  simp only [det_coshSum, ← prod_cosh_sPad]
  exact tendsto_finset_prod _ fun j _ => (Real.hasSum_cosh (sPad B j)).tendsto_sum_nat

theorem measurable_coshPow : ∀ (p q : ℕ) (c : ℝ), Measurable (coshPow c : UpqT p q → ℝ) := by
  intro p q c
  have : BorelSpace (UpqT p q) := (GlobalTheory.UpqTopology.upq_lcsc p q).2.2.2.2.1
  have h : Measurable fun g : UpqT p q =>
      ∏ i ∈ Finset.range (min p q), Real.cosh (singVal (cartanB g) i) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n (g : UpqT p q) => (coshSum n (cartanB g)).det.re) (fun n => ?_)
      (tendsto_pi_nhds.2 fun g => tendsto_det_coshSum _)
    exact (Complex.continuous_re.comp
      (((continuous_coshSum n).comp continuous_cartanB).matrix_det)).measurable
  have e : (coshPow c : UpqT p q → ℝ) = fun g =>
      (∏ i ∈ Finset.range (min p q), Real.cosh (singVal (cartanB g) i)) ^ (-c) := by
    funext g
    exact Real.finset_prod_rpow _ _ (fun i _ => (Real.cosh_pos _).le) _
  rw [e]
  exact h.pow_const _

end GlobalTheory.CoshPowMeas

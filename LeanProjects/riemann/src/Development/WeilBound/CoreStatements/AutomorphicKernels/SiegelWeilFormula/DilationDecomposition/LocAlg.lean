import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.WeightFactorEqAutomorphy
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussI

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

open PositivityTheory.Rg.Sw.Glob (aC ptZ jC gC actZ jF IsSiegel gZf)
open Matrix

variable {n : ℕ}

open PositivityTheory.Rg.Sw.Glob.GaussH in

theorem actZ_mul_K (y k : GR n) (hk : InK (mR k)) : actZ (y * k) (Complex.I • 1) = actZ y (Complex.I • 1) := by
  classical
  obtain ⟨hG, hU⟩ := hk
  have hmul : mR (y * k) = mR y * mR k := rfl
  set K := mR k with hKdef
  set Y := mR y with hYdef
  have hU' : K * Kᴴ = 1 := mul_eq_one_comm.mp hU
  have hcomm : JJ n * K = K * JJ n := by
    calc JJ n * K = (K * Kᴴ) * JJ n * K := by rw [hU', Matrix.one_mul]
      _ = K * (Kᴴ * JJ n * K) := by simp only [Matrix.mul_assoc]
      _ = K * JJ n := by rw [hG]
  have hKb : K = Matrix.fromBlocks K.toBlocks₁₁ K.toBlocks₁₂ K.toBlocks₂₁ K.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks K).symm
  have hYb : Y = Matrix.fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks Y).symm
  set A := K.toBlocks₁₁
  set B := K.toBlocks₁₂
  set C := K.toBlocks₂₁
  set D := K.toBlocks₂₂
  set P := Y.toBlocks₁₁
  set Q := Y.toBlocks₁₂
  set R := Y.toBlocks₂₁
  set S := Y.toBlocks₂₂
  rw [hKb] at hcomm hU
  simp only [JJ, Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_zero,
    Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, zero_add, add_zero, Matrix.fromBlocks_inj] at hcomm
  obtain ⟨hC, hD, -, -⟩ := hcomm
  rw [hC, hD] at hU
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_inj] at hU
  obtain ⟨h11, h12, -, -⟩ := hU
  have hK2 : K = Matrix.fromBlocks A B (-B) A := hKb.trans (by rw [hC, hD])
  set M := A - Complex.I • B with hMdef
  have hM : Mᴴ * M = 1 := by
    have key : Mᴴ * M = (Aᴴ * A + (-B)ᴴ * (-B)) - Complex.I • (Aᴴ * B + (-B)ᴴ * A) := by
      simp only [hMdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def,
        Complex.conj_I, Matrix.conjTranspose_neg, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, smul_smul]
      match_scalars <;> simp [Complex.I_sq] <;> ring
    rw [key, h11, h12, smul_zero, sub_zero]
  have hMdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hM
  have hMM : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMdet
  unfold actZ
  rw [hmul, hK2, hYb, Matrix.fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂]
  have hN : (P * A + Q * -B) * (Complex.I • 1) + (P * B + Q * A) = (P * (Complex.I • 1) + Q) * M := by
    simp only [hMdef, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, smul_smul, Complex.I_mul_I]
    match_scalars <;> simp [Complex.I_sq] <;> ring
  have hDn : (R * A + S * -B) * (Complex.I • 1) + (R * B + S * A) = (R * (Complex.I • 1) + S) * M := by
    simp only [hMdef, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_sub, Matrix.mul_neg, smul_smul, Complex.I_mul_I]
    match_scalars <;> simp [Complex.I_sq] <;> ring
  rw [hN, hDn, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc M, hMM, Matrix.one_mul]

open PositivityTheory.Rg.Sw.Glob.GaussH in
theorem gram_true_all {m : ℕ} (u : Fin m → Fin n → ℂ) :
    PositivityTheory.Rg.Sw.Glob.gramB (fun _ : Fin m => true) true u = (Matrix.of u)ᴴ * Matrix.of u := by
  ext i j
  simp [PositivityTheory.Rg.Sw.Glob.gramB, PositivityTheory.Rg.Sw.Qb, PositivityTheory.Rg.Sw.evX, Matrix.mul_apply, Matrix.conjTranspose_apply]

open PositivityTheory.Rg.Sw.Glob.GaussH in
theorem gram_false_all {m : ℕ} (u : Fin m → Fin n → ℂ) :
    PositivityTheory.Rg.Sw.Glob.gramB (fun _ : Fin m => true) false u = 0 := by
  ext i j
  simp [PositivityTheory.Rg.Sw.Glob.gramB, PositivityTheory.Rg.Sw.Qb, PositivityTheory.Rg.Sw.evX]

open PositivityTheory.Rg.Sw.Glob.GaussH in
theorem gramF_true {m : ℕ} (u : Fin m → Fin n → ℂ) :
    PositivityTheory.Rg.Sw.Glob.gramB (fun _ : Fin m => false) true u = 0 := by
  ext i j
  simp [PositivityTheory.Rg.Sw.Glob.gramB, PositivityTheory.Rg.Sw.Qb, PositivityTheory.Rg.Sw.evX]

open PositivityTheory.Rg.Sw.Glob.GaussH in
theorem gramF_false {m : ℕ} (u : Fin m → Fin n → ℂ) :
    PositivityTheory.Rg.Sw.Glob.gramB (fun _ : Fin m => false) false u = (Matrix.of u)ᴴ * Matrix.of u := by
  ext i j
  simp [PositivityTheory.Rg.Sw.Glob.gramB, PositivityTheory.Rg.Sw.Qb, PositivityTheory.Rg.Sw.evX, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem trace_aa {m : ℕ} (u : Fin m → Fin n → ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    ((a * aᴴ) * ((Matrix.of u)ᴴ * Matrix.of u)).trace = ((∑ i, ∑ j, ‖(Matrix.of u * a) i j‖ ^ 2 : ℝ) : ℂ) := by
  have h : ((a * aᴴ) * ((Matrix.of u)ᴴ * Matrix.of u)).trace =
      ((Matrix.of u * a) * (Matrix.of u * a)ᴴ).trace := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm (Matrix.of u)]
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

open PositivityTheory.Rg.Sw.Glob.GaussH in

theorem gzf_eval {m : ℕ} (s : ℤˣ) (b a : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) (u : Fin m → Fin n → ℂ) :
    gZf (fun _ : Fin m => true) (2 * Real.pi * ((s : ℤ) : ℝ)) (2 * Real.pi) (b + Complex.I • (a * aᴴ)) u =
      Complex.exp (2 * Real.pi * Complex.I * ((s : ℤ) : ℂ) * Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) *
        fP 1 (Matrix.of u * a) := by
  have hG := trace_aa u a
  have hfP : fP 1 (Matrix.of u * a) =
      Complex.exp (-(((2 * Real.pi * ∑ i, ∑ j, ‖(Matrix.of u * a) i j‖ ^ 2 : ℝ)) : ℂ)) := by
    simp [fP, PositivityTheory.Rg.Sw.gs, PositivityTheory.Rg.Sw.evX]
  rw [hfP, ← Complex.exp_add]
  rcases Int.units_eq_one_or s with hs | hs
  · subst hs
    have he : PositivityTheory.Rg.Sw.Glob.epsT (2 * Real.pi * (((1 : ℤˣ) : ℤ) : ℝ)) (fun _ : Fin m => true) =
        fun _ => true := by
      funext x
      simp [PositivityTheory.Rg.Sw.Glob.epsT, Real.pi_pos]
    unfold gZf
    rw [he, gram_true_all, gram_false_all, Matrix.mul_zero, Matrix.trace_zero, Matrix.add_mul,
      Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, hG]
    congr 1
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · subst hs
    have he : PositivityTheory.Rg.Sw.Glob.epsT (2 * Real.pi * (((-1 : ℤˣ) : ℤ) : ℝ)) (fun _ : Fin m => true) =
        fun _ => false := by
      funext x
      simp [PositivityTheory.Rg.Sw.Glob.epsT, Real.pi_pos.le]
    unfold gZf
    rw [he, gramF_true, gramF_false, Matrix.mul_zero, Matrix.trace_zero, Matrix.conjTranspose_add, hb,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.trace_smul, hG]
    congr 1
    simp only [Complex.star_def, Complex.conj_I, smul_eq_mul]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring

theorem iteratedDeriv_const_mul' (f : ℂ → ℂ) (c : ℂ) :
    ∀ r : ℕ, iteratedDeriv r (fun z => c * f z) = fun z => c * iteratedDeriv r f z := by
  intro r
  funext z
  exact iteratedDeriv_const_mul_field c f

theorem strip_ball (X : Fin n → ℝ) : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (0 : ℂ) ρ ⊆ strip X := by
  refine ⟨Real.pi / 4 / (∑ j, |X j| + 1), by positivity, ?_⟩
  intro z hz
  simp only [strip, Set.mem_setOf_eq]
  intro j
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hS : |X j| ≤ ∑ k, |X k| :=
    Finset.single_le_sum (f := fun k => |X k|) (fun k _ => abs_nonneg (X k)) (Finset.mem_univ j)
  have hz' : |z.im| < Real.pi / 4 / (∑ k, |X k| + 1) := lt_of_le_of_lt (Complex.abs_im_le_norm z) hz
  have hpos : 0 < ∑ k, |X k| + 1 := by positivity
  rw [abs_mul]
  calc |z.im| * |X j| ≤ |z.im| * (∑ k, |X k| + 1) := by gcongr; linarith
    _ < Real.pi / 4 / (∑ k, |X k| + 1) * (∑ k, |X k| + 1) := by gcongr
    _ = Real.pi / 4 := by field_simp

end PositivityTheory.SiegelWeilFormula.Kdil

end

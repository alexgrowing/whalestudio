import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyIteratedFDerivEqZeroOfRealSubspace
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.SingToDiffAlt

noncomputable section

open Filter Topology Set Metric Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.HolB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem JJ_sq : JJ n * JJ n = -1 := by
  simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem inG_mul {a b : M2 n} (ha : InG a) (hb : InG b) : InG (a * b) := by
  unfold InG at *
  rw [conjTranspose_mul]
  calc bᴴ * aᴴ * JJ n * (a * b) = bᴴ * (aᴴ * JJ n * a) * b := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [ha, hb]

theorem inG_upper {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (fromBlocks 1 b 0 1 : M2 n) := by
  unfold InG JJ
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hb]

theorem inG_lower {c : Matrix (Fin n) (Fin n) ℂ} (hc : cᴴ = c) : InG (fromBlocks 1 0 c 1 : M2 n) := by
  unfold InG JJ
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hc]

theorem inG_scalar {c : ℂ} (hc : star c * c = 1) : InG (c • (1 : M2 n)) := by
  show (c • (1 : M2 n))ᴴ * JJ n * (c • (1 : M2 n)) = JJ n
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm, hc, one_smul]

theorem upper_line (y : M2 n) (b : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    y + t • (y * fromBlocks 0 b 0 0) = y * fromBlocks 1 (t • b) 0 1 := by
  have e : (fromBlocks 1 (t • b) 0 1 : M2 n) = 1 + t • fromBlocks 0 b 0 0 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  rw [e, mul_add, mul_one, mul_smul_comm]

theorem lower_line (y : M2 n) (c : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    y + t • (y * fromBlocks 0 0 c 0) = y * fromBlocks 1 0 (t • c) 1 := by
  have e : (fromBlocks 1 0 (t • c) 1 : M2 n) = 1 + t • fromBlocks 0 0 c 0 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp
  rw [e, mul_add, mul_one, mul_smul_comm]

theorem herm_real_smul {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) (t : ℝ) : ((t : ℂ) • b)ᴴ = (t : ℂ) • b := by
  rw [conjTranspose_smul, hb]
  simp

private theorem fderiv_apply_eq_zero_of_const_on_real_line {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {f : E → W} {y v : E}
    (hf : DifferentiableAt ℂ f y) (h : ∀ t : ℝ, f (y + (t : ℂ) • v) = f y) : fderiv ℂ f y v = 0 := by
  have hl : HasDerivAt (fun t : ℝ => y + (t : ℂ) • v) v 0 := by
    have h0 := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).smul_const v).const_add y
    convert h0 using 1
    · rfl
    · rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]
  have h1 : HasFDerivAt f ((fderiv ℂ f y).restrictScalars ℝ) (y + ((0 : ℝ) : ℂ) • v) := by
    simpa using hf.hasFDerivAt.restrictScalars ℝ
  have hc := h1.comp_hasDerivAt (0 : ℝ) hl
  have hk : (f ∘ fun t : ℝ => y + (t : ℂ) • v) = fun _ => f y := funext h
  rw [hk] at hc
  exact ((hasDerivAt_const (0 : ℝ) (f y)).unique hc).symm

theorem fderiv_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {f : M2 n → W} {y v : M2 n}
    (hf : DifferentiableAt ℂ f y) (h : ∀ t : ℝ, f (y + (t : ℂ) • v) = f y) : fderiv ℂ f y v = 0 := by
  exact fderiv_apply_eq_zero_of_const_on_real_line hf h

end PositivityTheory.Rg.Sw.LVs.HolB

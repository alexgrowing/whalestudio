import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.OmegaLeast

open scoped Matrix.Norms.L2Operator in

theorem opNorm_le_sqrt_hs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ≤ Real.sqrt (Formalism.REAL.hs A) := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  have hhs : 0 ≤ Formalism.REAL.hs A := by unfold Formalism.REAL.hs; positivity
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, ← Real.sqrt_mul hhs]
  apply Real.sqrt_le_sqrt
  unfold Formalism.REAL.hs
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j‖ * ‖x j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖x j‖)
  refine le_trans ?_ h2
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

open scoped Matrix.Norms.L2Operator in

theorem opNorm_exp_le {n : ℕ} (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp A‖ ≤ Real.exp ‖A‖ := by
  have h1 : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = 1 := GlobalTheory.LeastVar.opN_one hn
  haveI : NormOneClass (Matrix (Fin n) (Fin n) ℂ) := ⟨h1⟩
  have h := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) A
  have h' := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) ‖A‖
  rw [Real.exp_eq_exp_ℝ]
  refine h.norm_le_of_bounded h' fun k => ?_
  rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq, norm_smul, smul_eq_mul]
  gcongr
  · simp
  · exact norm_pow_le _ _

open scoped Matrix.Norms.L2Operator in
theorem dOp_exp_mul_exp_le {n : ℕ} (hn : 1 ≤ n) (A Z : Matrix (Fin n) (Fin n) ℂ) :
    dOp (NormedSpace.exp A * NormedSpace.exp Z) ≤
      Real.sqrt (Formalism.REAL.hs A) + Real.sqrt (Formalism.REAL.hs Z) := by
  have h : ‖NormedSpace.exp A * NormedSpace.exp Z‖ ≤
      Real.exp (Real.sqrt (Formalism.REAL.hs A) + Real.sqrt (Formalism.REAL.hs Z)) := by
    rw [Real.exp_add]
    refine (norm_mul_le _ _).trans ?_
    gcongr
    · exact (opNorm_exp_le hn A).trans (Real.exp_le_exp.2 (opNorm_le_sqrt_hs A))
    · exact (opNorm_exp_le hn Z).trans (Real.exp_le_exp.2 (opNorm_le_sqrt_hs Z))
  change Real.log ‖NormedSpace.exp A * NormedSpace.exp Z‖ ≤ _
  rcases (norm_nonneg (NormedSpace.exp A * NormedSpace.exp Z)).eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; positivity
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem half_truncatedLeastLatticeSize_le_unipotentNeighbourhood : ∀ (I : AutInst) (x : I.GA) (W : Submodule I.E (Fin I.n → I.E)) (ρ : ℝ), 1 ≤ I.n → ρ ≤ Real.log 2 → ∀ y ∈ omega I x W ρ, tau1 I x / 2 ≤ tau1 I y := by
  intro I x W ρ hn hρ y hy
  obtain ⟨h2, A, Z, -, hAZ, hy1, -⟩ := hy
  obtain ⟨-, -, -, -, -, ⟨K, hK⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hk : (x⁻¹ * y).2 ∈ I.Kset := by
    have : (x⁻¹ * y).2 = 1 := by simp [h2]
    rw [this, ← hK]; exact K.one_mem
  have hv := GlobalTheory.LeastVar.truncatedLeastLatticeSize_rightTranslate_lower_bound I hn x (x⁻¹ * y) hk
  rw [mul_inv_cancel_left] at hv
  have hcard := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).2.2.1
  have hfpos : (0 : ℝ) < I.f := by
    rw [← hcard]; exact_mod_cast Fintype.card_pos
  have hhs : ∀ B : Matrix (Fin I.n) (Fin I.n) ℂ, 0 ≤ Formalism.REAL.hs B := fun B => by
    unfold Formalism.REAL.hs; positivity
  have hd : ∀ v, dOp (uMat ((x⁻¹ * y).1 v)) ≤ Real.log 2 := by
    intro v
    have e : uMat ((x⁻¹ * y).1 v) = NormedSpace.exp (A v) * NormedSpace.exp (Z v) := by
      have e1 : uMat ((x⁻¹ * y).1 v) = uMat ((x.1 v)⁻¹) * uMat (y.1 v) := by simp [uMat]
      have e2 : uMat ((x.1 v)⁻¹) * uMat (x.1 v) = 1 := by simp [uMat]
      rw [e1, hy1 v, Matrix.mul_assoc, ← Matrix.mul_assoc, e2, Matrix.one_mul]
    rw [e]
    refine (dOp_exp_mul_exp_le hn _ _).trans (le_trans ?_ (hAZ.trans hρ))
    gcongr
    · exact Finset.single_le_sum (f := fun v => Formalism.REAL.hs (A v)) (fun v _ => hhs _) (Finset.mem_univ v)
    · exact Finset.single_le_sum (f := fun v => Formalism.REAL.hs (Z v)) (fun v _ => hhs _) (Finset.mem_univ v)
  have hs : (∑ v, dOp (uMat ((x⁻¹ * y).1 v))) / I.f ≤ Real.log 2 := by
    rw [div_le_iff₀ hfpos]
    refine (Finset.sum_le_sum fun v _ => hd v).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_comm]
  have he : (1 / 2 : ℝ) ≤ Real.exp (-((∑ v, dOp (uMat ((x⁻¹ * y).1 v))) / I.f)) := by
    have : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [this]
    exact Real.exp_le_exp.2 (neg_le_neg hs)
  have ht : 0 ≤ tau1 I x := by
    obtain ⟨-, hfg, hspan, -, -⟩ := GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x
    haveI := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).1
    have hx := (GlobalTheory.Count.FrameMajorant.frames_give_majorants I x).2.2.2.2
    have hne : lamX I x ≠ ⊥ := by
      intro h
      haveI : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
      rw [h] at hspan
      simp at hspan
    have h3 := (sizeMu I.E _ _ (bas I) (frm I x) (fun w => (hx w).1) (lamX I x) hfg hne).2.2.2.1
    unfold tau1 least
    rw [h3]
    exact le_min (by norm_num) (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left he ht
  linarith

end GlobalTheory.OmegaLeast

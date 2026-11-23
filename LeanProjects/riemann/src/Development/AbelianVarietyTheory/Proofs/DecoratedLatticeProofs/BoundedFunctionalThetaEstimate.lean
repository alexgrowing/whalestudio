import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCost
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.CharDecay

open GlobalTheory.OrientedHeis Filter Topology

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem line_move (hθ : IsInfFam θ) {k l m n : ℕ} (P : Mx D k m) (Q : Mx D n l) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (compAt θ τ P ⬝ z ⬝ compAt θ τ Q) t = (P ⬝ lineAt θ τ z t ⬝ Q : Mx D k l) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ Mx D k l :=
    { toFun := fun t => P ⬝ lineAt θ τ z t ⬝ Q
      map_zero' := by rw [AddMonoidHom.map_zero, Matrix.mul_zero, Matrix.zero_mul]
      map_add' := fun s t => by rw [AddMonoidHom.map_add, Matrix.mul_add, Matrix.add_mul] }
  have hL' : IsLineAt θ τ (compAt θ τ P ⬝ z ⬝ compAt θ τ Q) L := by
    refine ⟨(continuous_const.matrix_mul hL.1).matrix_mul continuous_const, fun t => ?_, fun t τ' => ?_⟩
    · show (P ⬝ lineAt θ τ z t ⬝ Q : Mx D k l).map (finPart D) = 0
      rw [Matrix.map_mul, Matrix.map_mul, hL.2.1, Matrix.mul_zero, Matrix.zero_mul]
    · show compAt θ τ' (P ⬝ lineAt θ τ z t ⬝ Q : Mx D k l) = _
      rw [compAt_mul, compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul, Matrix.smul_mul]
      · rw [Matrix.mul_zero, Matrix.zero_mul]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

theorem phase_real (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {m n : ℕ} (y : Mx D n m) (κ : Mx D m n)
    (hκ : κ.map (finPart D) = 0) :
    ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ κ).trace)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((∑ τ, 2 * (Matrix.trace (compAt θ τ y ⬝ compAt θ τ κ)).re : ℝ) : ℂ)) := by
  set t := Matrix.trace (y ⬝ κ) with ht
  have hfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ κ hκ
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set R := Algebra.trace (AF D.host.F) (AE D) t with hR
  have h1 : ψ (-R) = psiInf D.host.F ψ (-(fstA D.host.F R)) := by
    unfold psiInf
    congr 1
    rw [hT]
    refine Prod.ext rfl ?_
    exact neg_zero
  have h2 := hψ.2.2 θ hθ (-(fstA D.host.F R))
  have h4 : ∀ ρ, θ ρ (infPart D t) = Matrix.trace (compAt θ ρ y ⬝ compAt θ ρ κ) := fun ρ => by
    simp only [ht, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply, compAt]
  have h3 : ∀ ρ, θ ρ ((-(fstA D.host.F R)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -((2 * (Matrix.trace (compAt θ ρ y ⬝ compAt θ ρ κ)).re : ℝ) : ℂ) := by
    intro ρ
    rw [TensorProduct.neg_tmul, map_neg, hR, GlobalTheory.PhaseReal.theta_trace θ hθ ρ t, h4]
  rw [h1, h2]
  congr 1
  simp only [h3, Finset.sum_neg_distrib]
  push_cast
  ring

theorem phase_line (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {m n : ℕ} (y : Mx D n m) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ lineAt θ τ z t).trace)) =
      Complex.exp (((4 * Real.pi * (Matrix.trace (compAt θ τ y ⬝ z)).re * t : ℝ) : ℂ) * Complex.I) := by
  have hL := isLineAt_lineAt hθ τ z
  rw [phase_real hψ hθ y _ (hL.2.1 t), Finset.sum_eq_single τ (fun τ' _ e => by
    rw [hL.2.2, if_neg e, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, mul_zero]) (by simp), hL.2.2, if_pos rfl,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  congr 1
  push_cast
  ring

theorem deriv_char (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (ℓ : (WO S T → ℂ) → ℂ)
    (hadd : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g)
    (hsmul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f)
    (hb : ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ) {L : ℝ →+ WO S T} (hL : IsRealDir T S L) (a : ℝ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (h : ∀ t : ℝ, ℓ (heisO ψ S T (L t) f) = Complex.exp (((a * t : ℝ) : ℂ) * Complex.I) * ℓ f) :
    ℓ (dLine ψ S T L f) = (a : ℂ) * Complex.I * ℓ f := by
  have hsub : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f - g) = ℓ f - ℓ g := fun f g hf hg => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ g, hadd _ _ hf (theta_smul _ hg), hsmul _ _ hg]
    ring
  obtain ⟨C, hC⟩ := quotient_bound hθ hψ hL hf
  have hd : HasDerivAt (fun t : ℝ => Complex.exp (((a * t : ℝ) : ℂ) * Complex.I)) ((a : ℂ) * Complex.I) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).const_mul a).ofReal_comp).mul_const Complex.I).cexp
    simpa using this
  have h1 := (hd.tendsto_slope_zero_right.mul_const (ℓ f)).sub_const (ℓ (dLine ψ S T L f))
  have h0 : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) := tendsto_id.const_mul C
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine (sub_eq_zero.1 (tendsto_nhds_unique h1 (squeeze_zero_norm' ?_ h0))).symm
  refine eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_
  have hH := theta_heisO_real hθ hψ (hL.2 t) hf
  have hq := theta_smul (t : ℂ)⁻¹ (theta_sub hH hf)
  have hD := theta_dLine hθ hψ hL hf
  have h2 := (hb _ (theta_sub hq hD)).trans (iSup_le fun w =>
    (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_ofReal (hC t ht w)))
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff ((norm_nonneg _).trans (hC t ht 0)), hsub _ _ hq hD,
    hsmul _ _ (theta_sub hH hf), hsub _ _ hH hf, h] at h2
  refine le_of_eq_of_le ?_ h2
  congr 2
  simp only [zero_add, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, Complex.real_smul, Complex.ofReal_inv]
  ring

theorem entry_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {m n : ℕ} (P : Mx D T.rank m) (Q : Mx D n S.rank)
    (ℓ : (WO S T → ℂ) → ℂ) (y : Mx D n m)
    (hadd : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g)
    (hsmul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f)
    (hb : ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ)
    (hchar : ∀ (ξ : Mx D m n) f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (P ⬝ ξ ⬝ Q) f) =
      ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * ℓ f)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (i : Fin n) (j : Fin m) :
    ‖ℓ f‖ₑ * ENNReal.ofReal ‖compAt θ τ y i j‖ ≤
      ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ P ⬝ single j i (1 : ℂ) ⬝ compAt θ τ Q) f)‖ₑ +
      ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ P ⬝ single j i Complex.I ⬝ compAt θ τ Q) f)‖ₑ := by
  have key : ∀ b : ℂ, ‖ℓ f‖ * |(compAt θ τ y i j * b).re| ≤
      ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (compAt θ τ P ⬝ single j i b ⬝ compAt θ τ Q) f)‖ := fun b => by
    rw [dRho_eq_dLine, deriv_char hψ hθ ℓ hadd hsmul hb (isRealDir_lineAt hθ τ _)
      (4 * Real.pi * (Matrix.trace (compAt θ τ y ⬝ single j i b)).re) hf fun t => by
        rw [line_move hθ, hchar _ f hf, phase_line hψ hθ], Matrix.trace_mul_single, op_smul_eq_mul, norm_mul, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 4 * Real.pi),
      mul_comm]
    refine mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (abs_nonneg _) ?_) (norm_nonneg _)
    linarith [Real.pi_gt_three]
  have k1 := key 1
  have k2 := key Complex.I
  rw [mul_one] at k1
  rw [Complex.mul_I_re, abs_neg] at k2
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (le_trans ?_ (add_le_add k1 k2))
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im _) (norm_nonneg _)

end GlobalTheory.CharDecay

theorem GlobalTheory.CharDecay.decay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (m n : ℕ) (P : Mx D T.rank m) (Q : Mx D n S.rank) (N : ℕ), ∃ C : ℝ≥0, ∀ (ℓ : (WO S T → ℂ) → ℂ) (y : Mx D n m), (∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g) → (∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f) → (∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ ≤ ⨆ w, ‖f w‖ₑ) → (∀ (ξ : Mx D m n) f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (P ⬝ ξ ⬝ Q) f) = ψ (-(Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace)) * ℓ f) → ∀ f, IsThetaFunO ψ S T f → ‖ℓ f‖ₑ * ENNReal.ofReal ((1 + realSize θ y) ^ N) ≤ C * supSob ψ θ N f := by
  intro D ψ hψ θ hθ S T m n P Q N
  have hc : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), ∃ c : ℝ≥0, ∀ k (f : WO S T → ℂ),
      IsThetaFunO ψ S T f →
        supSob ψ θ k (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) ≤ c * supSob ψ θ (k + 1) f := fun τ z =>
    ⟨Real.toNNReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)), fun k f hf =>
      GlobalTheory.Size.SupWord.ws_dRho_le (p := fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) hψ hθ GlobalTheory.Size.SupWord.supN_add_le
        GlobalTheory.Size.SupWord.supN_smul hf τ z k⟩
  choose c hc using hc
  induction N with
  | zero =>
    refine ⟨1, fun ℓ y _ _ hb _ f hf => ?_⟩
    rw [pow_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_one, one_mul]
    unfold supSob
    rw [GlobalTheory.Size.wordSum_zero]
    exact hb f hf
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C + ∑ τ, ∑ i : Fin n, ∑ j : Fin m, (C * c τ (compAt θ τ P ⬝ single j i (1 : ℂ) ⬝ compAt θ τ Q) +
      C * c τ (compAt θ τ P ⬝ single j i Complex.I ⬝ compAt θ τ Q)), fun ℓ y hadd hsmul hb hchar f hf => ?_⟩
    have hs := realSize_nonneg θ y
    have hd : ∀ τ z, ‖ℓ (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f)‖ₑ * ENNReal.ofReal ((1 + realSize θ y) ^ N) ≤
        (C * c τ z : ℝ≥0) * supSob ψ θ (N + 1) f := fun τ z => by
      refine (hC ℓ y hadd hsmul hb hchar _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ τ z hf)).trans ?_
      rw [ENNReal.coe_mul, mul_assoc]
      exact mul_le_mul_right (hc τ z N f hf) _
    have he : ENNReal.ofReal (realSize θ y) = ∑ τ, ∑ i, ∑ j, ENNReal.ofReal ‖compAt θ τ y i j‖ := by
      unfold realSize
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
    rw [pow_succ, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add zero_le_one hs, ENNReal.ofReal_one, he,
      ← mul_assoc, mul_add, mul_one, ENNReal.coe_add, add_mul]
    refine add_le_add ((hC ℓ y hadd hsmul hb hchar f hf).trans
      (mul_le_mul_right (GlobalTheory.Size.wordSum_mono (Nat.le_succ N) f) _)) ?_
    simp only [ENNReal.ofNNReal_finsetSum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [mul_right_comm, ENNReal.coe_add, add_mul]
    refine (mul_le_mul_left (GlobalTheory.CharDecay.entry_le hψ hθ P Q ℓ y hadd hsmul hb hchar hf τ i j) _).trans ?_
    rw [add_mul]
    exact add_le_add (hd τ _) (hd τ _)

end

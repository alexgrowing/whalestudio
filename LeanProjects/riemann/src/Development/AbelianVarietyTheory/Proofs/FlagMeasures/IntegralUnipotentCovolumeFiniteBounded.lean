import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBoundsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LebesgueCommonStabilizerEqRadicalLeviMapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentEqLebesgueStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOnStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairInnerLatticesUnimodularPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseNormalFormRealFramesAtRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsBaseLatticeStabilizerFixedFrameUnipoteStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetUnipotentOnBesselModelsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealIntegralUnipotentBesselModelsCountableSubgroStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfStrictFundamentalSetsPlacewiseStatement
noncomputable section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem covN_haarLie_smul {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (κ : ℝ≥0∞) :
    haarLie S κ = κ • haarLie S 1 := by
  unfold haarLie; rw [one_smul]

theorem covN_muNB_one (D : D7) : muNB D 1 =
    (kapN D 1 * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) • GlobalTheory.Amp.lebN D.R.k D.R.rS := by
  rw [muNB, covN_haarLie_smul, GlobalTheory.T.haar_lie_nilpotent_eq_lebesgue, smul_smul]

theorem covN_pi_smul {ι : Type} [Fintype ι] {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (c : ℝ≥0) : Measure.pi (fun _ : ι => (c : ℝ≥0∞) • μ) = ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  haveI : SigmaFinite ((c : ℝ≥0∞) • μ) := by
    first
    | (have h : ((c : ℝ≥0∞) • μ) = c • μ := (ENNReal.smul_def c μ).symm
       rw [h]; infer_instance)
    | (rw [← ENNReal.smul_def]; infer_instance)
  refine (Measure.pi_eq fun s hs => ?_)
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

theorem covN_arith (v : ℝ) (hv : 1 ≤ v) (r k f : ℕ) :
    1 ≤ ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * v ^ (k * r * f) := by
  have hv0 : 0 < v := by linarith
  have h2v : 0 < 2 * v := by linarith
  have hA : (2 * v) ^ (-((r : ℝ) * k)) * v ^ (k * r) = ((2 : ℝ) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg h2v.le, show ((r : ℝ) * k) = ((r * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, mul_pow,
      show k * r = r * k from Nat.mul_comm k r]
    have : (0 : ℝ) < v ^ (r * k) := pow_pos hv0 _
    field_simp
  have hB : ((2 * v) ^ (-((r : ℝ) * k)) * 1 * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f * v ^ (k * r * f) =
      (((2 : ℝ) ^ (r * k))⁻¹ * 2 ^ (r * (k + 1) + r * (r - 1))) ^ f := by
    rw [← hA, pow_mul, ← mul_pow]
    ring
  rw [hB]
  apply one_le_pow₀
  rw [← div_eq_inv_mul, one_le_div (by positivity)]
  apply pow_le_pow_right₀ (by norm_num)
  nlinarith [Nat.zero_le (r * (r - 1))]

theorem covNC_holds : CovNC := by
  intro D large₂ X Y u C hS
  obtain ⟨hCM, hPl, hv, hv1, -, hcard, -, -, -, hnorm, hfin, hg2, -⟩ := GlobalTheory.T.unitaryHostFieldArithmeticConditions D large₂ hS
  obtain ⟨N, hF, hF', hj, hT, h𝔡, hTerm, hRef, hist⟩ := GlobalTheory.T.fixedFrameSelfNormalFormExists_proof D large₂ X Y u hS (VS D).L0 (Or.inr rfl)
  obtain ⟨hU, -, hz, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive D.host.E (VS D).V (HV D) hCM D.R.rS N (gS D) (VS D).L0 (by omega) hTerm
  have hzL : N.F.z ∈ GlobalTheory.HermLat.latL N.F N.F' (VS D).L0 := by
    have h := (hz 1).2 (by simp)
    simpa using h
  have hFr := GlobalTheory.T.baseNormalForm_realFrames_at_realPlaces D large₂ X u C hS N hF hF' hj hT (hist rfl)
  have hN𝔡 : (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) ^ (2 * Fintype.card D.what₂.Tau) := by
    rw [h𝔡, hnorm, hv, hcard]
  have hv1' : 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E := by rw [hv]; exact hv1
  obtain ⟨Ω, hΩ, hlo, hhi⟩ := GlobalTheory.T.covolume_referenceLattice_stabiliser_bounds D.host.E (VS D).V (HV D) hCM D.R.rS N D.R.k D.what₂.Tau (embS D)
    (fun _ => 0) (fun τ => phiV C τ) (fun τ => zB X (C.Qi τ) u τ) (fun τ => zB X (C.Qi τ) u τ) (fun _ => 1)
    hPl hfin hFr hN𝔡 hv1' _ hU hzL
  rw [hRef, GlobalTheory.T.real_points_base_lattice_stabilizer_fixed_frame_unipotent D large₂ X Y u C hS N hF hF'] at hΩ
  have hsw := (GlobalTheory.T.lebesgueCommonStabilizer_eq_radical_levi_map D.R.k D.R.rS N.j (fun _ => 0) monotone_const (by intro a b _; simp [hj])).2.2.2 hj
  rw [hsw, hj, hv, hcard, Nat.sub_zero] at hlo hhi
  obtain ⟨hc, h1, hmul, hinv, hNs⟩ := GlobalTheory.T.realIntegralUnipotent_besselModels_countable_subgroup D X Y u C
  have heq := GlobalTheory.T.measure_eq_of_strictFundamentalSetsPlacewise D.what₂.Tau D.R.k D.R.rS _ _ _ hc h1 hmul hinv hNs hΩ (GlobalTheory.T.strictFundamentalSet_unipotent_on_besselModels D X Y u C)
  haveI : SigmaFinite (GlobalTheory.Amp.lebN D.R.k D.R.rS) := (GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn D.R.k D.R.rS).1
  set c : ℝ≥0 := ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1).toNNReal *
    2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) with hc_def
  have hk : kapN D 1 * 2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1)) = (c : ℝ≥0∞) := by
    rw [hc_def, kapN, ENNReal.ofReal]
    push_cast
    rfl
  have hcov : covN C Y u = (c : ℝ≥0∞) ^ D.R.f * Measure.pi (fun _ : D.what₂.Tau => GlobalTheory.Amp.lebN D.R.k D.R.rS) Ω := by
    rw [covN, covN_muNB_one, hk, covN_pi_smul, Measure.smul_apply, smul_eq_mul, hcard, ← heq]
  have hfinΩ : Measure.pi (fun _ : D.what₂.Tau => GlobalTheory.Amp.lebN D.R.k D.R.rS) Ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hhi
  have hne : covN C Y u ≠ ⊤ := by
    rw [hcov]; exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hfinΩ
  refine ⟨hne, ?_⟩
  have hlo' := (ENNReal.ofReal_le_iff_le_toReal hfinΩ).1 hlo
  have hlpos : 0 < lossV D := by
    unfold lossV; exact pow_pos (by linarith) _
  have hcr : ((c : ℝ≥0∞) ^ D.R.f).toReal = ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f := by
    rw [ENNReal.toReal_pow, ENNReal.coe_toReal, hc_def, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
    push_cast; ring
  rw [hcov, ENNReal.toReal_mul, hcr]
  have key := covN_arith D.host.v hv1 D.R.rS D.R.k D.R.f
  have hpos : 0 ≤ ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
      2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f := by positivity
  have hq : D.host.v ^ (D.R.k * D.R.rS * D.R.f) / (8 * D.host.v) ^ (2 * (D.R.rS + 1) ^ 2 * D.R.f) * lossV D =
      D.host.v ^ (D.R.k * D.R.rS * D.R.f) := by
    unfold lossV; field_simp
  calc (1 : ℝ) ≤ ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f * D.host.v ^ (D.R.k * D.R.rS * D.R.f) := key
    _ = ((2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * 1 *
        2 ^ (D.R.rS * (D.R.k + 1) + D.R.rS * (D.R.rS - 1))) ^ D.R.f *
        (D.host.v ^ (D.R.k * D.R.rS * D.R.f) / (8 * D.host.v) ^ (2 * (D.R.rS + 1) ^ 2 * D.R.f) * lossV D) := by rw [hq]
    _ ≤ _ := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hlpos.le
      exact mul_le_mul_of_nonneg_left hlo' hpos

end GlobalTheory.TypeAsm

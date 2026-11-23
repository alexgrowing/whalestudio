import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableBcWeight

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp

open SchurBound

theorem schurSt_of_big_tie_uniform : ∀ Cg cb Cu cT CT C1 : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl C0 : ℝ), Big D large₂ Cl m₀ → cdScaleTie D → BSch D large₂ C' Cl Cg cb Cu cT CT C0 → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 → SchurSt D large₂ C' Cl Cg cb Cu cT CT C0 C1 C := by
  intro Cg cb Cu cT CT C1
  refine ⟨2 * |CT| + 2 * C1, fun C hC => ⟨0, ?_⟩⟩
  intro D large₂ C' Cl C0 hBig htie hB hL hZ τ w w' hTT θ hθ W hW A hA μsec hsec
  obtain ⟨-, -, hb, hm, hr, -, -, hk, hv, -, -, -, -, -, -, -, hTb, -, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hBig.1 hZ
  have hb1 : 1 ≤ large₂.sc.b := by linarith [Real.add_one_le_exp 1]
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hθ.1
  have hv0 : 0 < D.host.v := by linarith
  have hm1 : 1 ≤ D.R.m := by omega
  have hk1 : 1 ≤ D.R.k := le_trans (Nat.one_le_pow _ _ hm1) hk
  have hT : 0 < Tr D w := by unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by unfold Tr; exact_mod_cast hTT.2.1.pos
  obtain ⟨hU, hI, -, hS, hS'⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W _ A hθ0 hv0 hTT hW hA
  obtain ⟨hM, hM', hDec⟩ := hL hZ τ w w' θ W hTT hW A hA
  have hBS := hB hZ τ w w' θ W hW A hA hT
  have hBS' := hB hZ τ w' w θ (swapW W) (goodW_swap hW) (swapS A) (goodS_swap hA) hT'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, -, -, s13, s14, s15⟩ := hS
  obtain ⟨t1, t2, t3, t4, t5, -, t7, t8, -, t10, -, -, t13, -, t15⟩ := hS'
  obtain ⟨-, -, -, -, hz, hz', -, -, -, -, -, hN, -, -⟩ := hW
  obtain ⟨-, -, a3, a4, a5, a6, -, -, -, -, P, hP, hdeg⟩ := hA
  obtain ⟨c, hc, hdens, -⟩ := GlobalTheory.T.exists_unique_haarDensity_at_identity _ (GG D.R.k D.R.rS) W.μG (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group _ _) s6
  have hSch := GlobalTheory.T.besselModel_schur_of_formalDegree_density D.R.k D.R.rS A.σ (epsSH D.R) D.cd _ P A.deg c W.μG (htie _ _) hP hdeg hc s6 hdens
  have hd : 0 < A.deg := hdeg.1
  set κ : ℝ := (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ with hκ
  have hκ0 : 0 < κ := mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ0
  obtain ⟨hmeas, hdis⟩ := GlobalTheory.T.besselDoubleCosetMeasure_bigCell_eq D.R.k D.R.rS W.z W.z' μsec W.μG W.μW W.μW' c κ hk1 s1 t1 s2 t2 hsec hc hκ0
    s6 hdens s7 s8 t7 t8
  have hN' : haarLie (Nset D.R.k D.R.rS) (ENNReal.ofReal κ) = W.μN := hN.symm
  rw [hN'] at hdis
  have hnv : ‖A.v0‖ ≠ 0 := norm_ne_zero_iff.2 a6
  have hstd : StdSm A.σ (((‖A.v0‖ : ℝ) : ℂ)⁻¹ • A.v0) (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 5) W.μG
      (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1))) := by
    refine ⟨⟨hk1, hU, hI, ?_, s6, hSch, le_rfl, hDec.mono (DD_smul_le _ _ _), inferInstance⟩, smooth_smul _ _ _ a5⟩
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hnv]
  unfold psiS at hM hM' a3 a4
  rw [psi_eq_psiGen] at hM hM' a3 a4
  have hQ := GlobalTheory.T.lintegral_hilbertSchmidtNormSq_besselAmplitude_le D.R.k D.R.rS A.σ A.v0 _ _ A.cN W.μG _ _ W.νS W.νS' _ W.z W.z' _ _ W.π W.π' A.B A.B' a6 hstd
    ⟨⟨s1, s2, s4, GlobalTheory.T.isHaarOn_besselSubgroup_prod_map _ _ _ _ _ s1 s2 s7 s9, inferInstance⟩, s5, s3⟩
    ⟨⟨t1, t2, t4, GlobalTheory.T.isHaarOn_besselSubgroup_prod_map _ _ _ _ _ t1 t2 t7 s9, inferInstance⟩, t5, t3⟩
    s10 t10 hM hM' a3 a4 s14 s15 t15 hBS hBS' hdis
  have hFm := GlobalTheory.T.measurable_hsNormSq_amplitude_besselUnitary D.R.k D.R.rS W.μG A.cN A.Φ A.Φ' s6 s13 t13
  have hvk := volUn_pos D.R.k
  have hvk1 := volUn_pos (D.R.k - 1)
  have hvn := volUn_pos (2 * D.R.rS + D.R.k + 1)
  set a : ℝ := c * 2 ^ (D.R.rS + 1) * volUn D.R.k ^ 2 / volUn (D.R.k - 1) /
    (Tz D.R.k D.R.rS W.z * Tz D.R.k D.R.rS W.z') ^ D.R.k / κ ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have hcell := lintegral_cell volume _ (measurable_bcWeight D.R.k D.R.rS _ _) (bcWeight_nonneg _ _ _ _) _ _ _ a ha0 hmeas
    (measure_mono_null (fun x hx h => hx (Greg_subset _ _ h)) hdis.2.1) hFm
  have hMM : ENNReal.ofReal a * MMv D w w' A μsec ≤ ENNReal.ofReal ((Module.finrank ℂ W.Wp : ℝ) * Module.finrank ℂ W.Wq /
      (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1)))) := by
    refine le_trans (le_of_eq ?_) hQ
    unfold MMv
    rw [← hz, ← hz']
    exact hcell.symm
  have hMM2 : MMv D w w' A μsec ≤ ENNReal.ofReal (((Module.finrank ℂ W.Wp : ℝ) * Module.finrank ℂ W.Wq /
      (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1)))) / a) := by
    rw [ENNReal.ofReal_div_of_pos ha0, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ha0)) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact hMM
  refine hMM2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hf := factor_le large₂.sc.b D.R.m (Tr D w) (Tr D w') θ CT C1 C D.R.rS hb1 (by exact_mod_cast hm1) hT hT' hθ0
    (hTb w) (hTb w') hθ.2 hC
  have hκ2 : κ ^ 2 = θ ^ 2 / (2 * D.host.v) ^ (2 * D.R.rS * D.R.k) := by
    rw [hκ, Real.rpow_neg (by linarith), ← Nat.cast_mul, Real.rpow_natCast, mul_assoc 2, mul_comm 2 (D.R.rS * D.R.k),
      pow_mul _ _ 2]
    field_simp
  have hpow : (Tr D w * Tr D w') ^ D.R.k = (Tr D w * Tr D w') ^ (D.R.k - 1) * (Tr D w * Tr D w') := by
    rw [← pow_succ, Nat.sub_add_cancel hk1]
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hf ?_)
  · rw [ha, hz, hz', hκ2, hpow, hr]
    field_simp
  · have := volUn_pos D.R.r
    positivity

end GlobalTheory.Amp

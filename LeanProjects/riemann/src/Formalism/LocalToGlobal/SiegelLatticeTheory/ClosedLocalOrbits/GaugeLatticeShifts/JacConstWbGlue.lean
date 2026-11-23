import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB Formalism.L2.SG.Pf.Jac

variable {k r : ℕ}

def gA (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r) : Mt k r :=
  fun i j => ((Matrix.of a)⁻¹ * E * Matrix.of b) i j

def gB (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r) : Mt k r :=
  fun i j => (Matrix.of a * E * (Matrix.of b)⁻¹) i j

theorem meas_gA (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun p : Mt k r × Mt k r => f (gA E p.1 p.2) := by
  have e : (fun p : Mt k r × Mt k r => gA E p.1 p.2) = fun p =>
      (fun i j => (Matrix.of (fun i j => (Matrix.of (fun i j => ((Matrix.of p.1)⁻¹) i j : Mt k r) *
        Matrix.of (E : Mt k r)) i j : Mt k r) * Matrix.of p.2) i j : Mt k r) := by
    funext p; rfl
  have : Measurable fun p : Mt k r × Mt k r => gA E p.1 p.2 := by
    rw [e]
    exact mulMt_meas (mulMt_meas (invMt_meas measurable_fst) measurable_const) measurable_snd
  exact hf.comp this

theorem meas_gB (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun p : Mt k r × Mt k r => f (gB E p.1 p.2) :=
  hf.comp (meas_PQinv (fun p : Mt k r × Mt k r => Matrix.of p.1 * E) (fun p => Matrix.of p.2) (by fun_prop) (by fun_prop))

theorem measurable_comp_group_action (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a0 : Mt k r) {f : Mt k r → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun b : Mt k r => f (gA E a0 b) := by
  let P : Mt k r → Mt k r := fun b =>
    ((Matrix.of a0)⁻¹ * E * Matrix.of b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  have hP : Continuous P := by
    show Continuous fun b : Mt k r =>
      ((Matrix.of a0)⁻¹ * E * Matrix.of b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    fun_prop
  exact hf.comp hP.measurable

theorem gA_inv (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a b : Mt k r)
    (ha : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det) :
    gA E (Formalism.FourierDecayAlt.B2.invM a) (Formalism.FourierDecayAlt.B2.invM b) = gB E a b := by
  have h1 : ((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ = Matrix.of a :=
    Matrix.nonsing_inv_nonsing_inv _ ha
  show (fun i j => (((Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹)⁻¹ * E *
      (Matrix.of b)⁻¹) i j : Mt k r) = fun i j => (Matrix.of a * E * (Matrix.of b)⁻¹) i j
  rw [h1]

theorem prod_to_iter {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z')
    (hT' : 0 < Tz k r z') {μW μW' : Measure (Mt k r)} (hW : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μW)
    (hW' : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z') μW') (E : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p : Mt k r × Mt k r, f ((Matrix.of p.1)⁻¹ * E * Matrix.of p.2) ∂(μW.prod μW') =
      ∫⁻ h, ∫⁻ h', f (fun i j => (Matrix.of h * E * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW := by
  have sW := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW
  have sW' := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW'
  have hinv : μW.map Formalism.FourierDecayAlt.B2.invM = μW :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z) μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hW
  have hinv' : μW'.map Formalism.FourierDecayAlt.B2.invM = μW' :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion k r (UWset k r z') μW' (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z') hW'
  have hA := meas_gA (k := k) (r := r) E hf
  have e0 : (fun p : Mt k r × Mt k r => f ((Matrix.of p.1)⁻¹ * E * Matrix.of p.2)) = fun p => f (gA E p.1 p.2) := by
    funext p; rfl
  rw [e0, lintegral_prod (fun p : Mt k r × Mt k r => f (gA E p.1 p.2)) hA.aemeasurable]
  have key : ∀ (ν : Measure (Mt k r)), ν.map Formalism.FourierDecayAlt.B2.invM = ν → ∀ F : Mt k r → ℝ≥0∞, Measurable F →
      ∫⁻ a, F a ∂ν = ∫⁻ a, F (Formalism.FourierDecayAlt.B2.invM a) ∂ν := by
    intro ν hν F hF
    conv_lhs => rw [← hν]
    exact lintegral_map hF Formalism.FourierDecayAlt.P.B2x1.invM_meas
  refine (key μW hinv _ hA.lintegral_prod_right').trans ?_
  have hae : ∀ᵐ a ∂μW, (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UWset k r z :=
    ae_iff.2 hW.conc
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with a ha
  have hau : IsUnit (Matrix.of a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det := unit_of_UH ha.1
  refine (key μW' hinv' _ (measurable_comp_group_action E (Formalism.FourierDecayAlt.B2.invM a) hf)).trans ?_
  refine lintegral_congr fun b => ?_
  rw [gA_inv E a b hau]
  rfl

theorem rhsWHaar : RhsWHaar := by
  intro k r z z' μW μW' a a' μsec D
  obtain ⟨μb0, hb0⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  have hW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 k r z μW D.z_mem D.T_pos D.haarW
  have hW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 k r z' μW' D.z'_mem D.T'_pos D.haarW'
  obtain ⟨C, hC, hI⟩ := Formalism.FourierDecayAlt.P.rank_one_integration_formula k r z z' μsec μb0 μW μW' D.k_pos D.z_mem D.z'_mem
    D.T_pos D.T'_pos D.sec hb0 hW hW'
  refine ⟨C⁻¹ • μb0, isHaarOn_smul (skHaar_of_cs hb0) (inv_pos.2 hC), fun φ hφ => ?_⟩
  rw [lintegral_smul_measure, hI φ hφ]
  unfold rhsW
  simp_rw [prod_to_iter D.z_mem D.T_pos D.z'_mem D.T'_pos hW hW' _ hφ]
  rw [ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hC.ne', ENNReal.coe_one, one_mul]

theorem mBase_mem {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (hsec : IsSection k r z z' μsec) :
    mBase k r z z' μsec ∈ Formalism.FourierDecayAlt.B2.UWb k r := by
  have hlt : Tz k r z * Tz k r z' < Complex.normSq (zeta0 k r z z') := by
    have hp : 0 < Tz k r z * Tz k r z' := mul_pos hT hT'
    unfold zeta0
    rw [Complex.normSq_ofReal]
    have hs := Real.mul_self_sqrt hp.le
    have e : (2 * Real.sqrt (Tz k r z * Tz k r z')) * (2 * Real.sqrt (Tz k r z * Tz k r z')) =
        4 * (Real.sqrt (Tz k r z * Tz k r z') * Real.sqrt (Tz k r z * Tz k r z')) := by ring
    rw [e, hs]
    linarith
  exact (Formalism.FourierDecayAlt.P.unipotent_weyl_properties k r).1 ▸ ⟨_, (hsec.2 _ hlt).1, rfl⟩

theorem gaugeShiftW : GaugeShiftW := by
  intro k r z z' μb μW μW' a a' μsec D hμb ρ hρ
  have hg : MeasurableSet (bBall k r ρ) := measurableSet_expBall (k := k) (r := r) (Formalism.FourierDecayAlt.B2.UWb k r) ρ hρ
  have hmem : (mBase k r z z' μsec)⁻¹ ∈ Formalism.FourierDecayAlt.B2.UWb k r :=
    (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r).inv_mem _ (mBase_mem D.T_pos D.T'_pos D.sec)
  have hl : Measurable (lmulM (k := k) (r := r) (mBase k r z z' μsec)⁻¹) := by
    have : Continuous (lmulM (k := k) (r := r) (mBase k r z z' μsec)⁻¹) := by
      show Continuous fun x : Mt k r =>
        ((mBase k r z z' μsec)⁻¹ * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      exact continuous_const.matrix_mul continuous_id
    exact this.measurable
  have e : mBall k r z z' μsec ρ = lmulM (mBase k r z z' μsec)⁻¹ ⁻¹' bBall k r ρ := rfl
  refine ⟨e ▸ hl hg, ?_⟩
  rw [e, ← Measure.map_apply hl hg, hμb.2.2.2 _ hmem]

theorem wbDataEx : WbDataEx := by
  intro k r hk
  set z : Fin (2 * r + k + 1) → ℂ := Formalism.L2.SG.Pf.WFL.zBv k r 1 with hz
  have hzW : inWb k r z := Formalism.L2.SG.Pf.WFL.inWb_zB 1
  have hzT : Tz k r z = 1 := Formalism.L2.SG.Pf.WFL.Tz_zB zero_le_one
  have hT : 0 < Tz k r z := by rw [hzT]; exact one_pos
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hzW hT
  have hcpt := Formalism.FourierDecayAlt.P.weyl_subgroup_compact k r z hzW hT
  have hfin : μ Set.univ < ⊤ := by
    have h1 : μ Set.univ ≤ μ (UWset k r z : Set (Mt k r)) + μ (UWset k r z : Set (Mt k r))ᶜ := by
      have := measure_union_le (μ := μ) (UWset k r z : Set (Mt k r)) (UWset k r z : Set (Mt k r))ᶜ
      rwa [Set.union_compl_self] at this
    have h2 : μ (UWset k r z : Set (Mt k r))ᶜ = 0 := hμ.conc
    have h3 : μ (UWset k r z : Set (Mt k r)) < ⊤ := hμ.finite_compact _ hcpt
    rw [h2, add_zero] at h1
    exact lt_of_le_of_lt h1 h3
  have h0 : μ Set.univ ≠ 0 := fun h => hμ.ne_zero (Measure.measure_univ_eq_zero.1 h)
  obtain ⟨μsec, hsec⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k r z z hk hzW hzW hT hT
  have ha : 0 < (μ Set.univ).toReal := ENNReal.toReal_pos h0 hfin.ne
  have hm : μ Set.univ = ENNReal.ofReal (μ Set.univ).toReal := (ENNReal.ofReal_toReal hfin.ne).symm
  exact ⟨z, z, μ, μ, _, _, μsec, ⟨hk, hzW, hzW, hT, hT, skHaar_of_cs hμ, skHaar_of_cs hμ, ha, ha, hm, hm, hsec⟩⟩

end Formalism.L2.SG.Pf.GE

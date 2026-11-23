import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacLocOfHpk
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarTranslationMeasurability

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem meas_invM : Measurable (invM : Mt k r → Mt k r) := by
  unfold invM
  have hof : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  have hc : Continuous fun x : Mt k r => ((Matrix.of x).adjugate : Mt k r) := hof.matrix_adjugate
  have hdc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r).det := hof.matrix_det
  have hd : Measurable fun x : Mt k r => Ring.inverse (Matrix.of x : Mat k r).det := by
    simp only [Ring.inverse_eq_inv']
    exact hdc.measurable.inv
  have he : (fun x : Mt k r => (((Matrix.of x : Mat k r)⁻¹ : Mat k r) : Mt k r)) =
      fun x : Mt k r => (Ring.inverse (Matrix.of x).det • (Matrix.of x).adjugate : Mt k r) := by
    funext x
    rw [Matrix.inv_def]
  have hc' : Measurable fun x : Mt k r => ((Matrix.of x).adjugate : Mt k r) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable
  rw [he]
  exact hd.smul hc'

theorem meas_mulM : Measurable (mulM : Mt k r × Mt k r → Mt k r) := by
  unfold mulM
  have hc : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mat k r)) :=
    Continuous.matrix_mul continuous_fst continuous_snd
  exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
    ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable

def Cm (g : Mt k r) (p : SS k r) : Mt k r := mulM (mulM (mulM (mulM (p.1.1, p.1.2), g), p.2.2), p.2.1)

def Tm (g : Mt k r) (p : Mt k r × Mt k r) : Mt k r := mulM (mulM (p.1, g), invM p.2)

theorem meas_Cm (g : Mt k r) : Measurable (Cm g) := by
  unfold Cm
  have hm := meas_mulM (k := k) (r := r)
  exact hm.comp ((hm.comp ((hm.comp ((hm.comp (measurable_fst.fst.prodMk measurable_fst.snd)).prodMk
    measurable_const)).prodMk measurable_snd.snd)).prodMk measurable_snd.fst)

theorem meas_Tm (g : Mt k r) : Measurable (Tm g) := by
  unfold Tm
  have hm := meas_mulM (k := k) (r := r)
  exact hm.comp ((hm.comp (measurable_fst.prodMk measurable_const)).prodMk (meas_invM.comp measurable_snd))

theorem tgt_eq (A B A' : Measure (Mt k r)) [SFinite A] [SFinite B] [SFinite A']
    (hB : B.map invM = B) (hA' : A'.map invM = A') (g : Mt k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ s, ∫⁻ s', φ (Tm g (s, s')) ∂(Formalism.MainNotions.S.muS A' B) ∂(Formalism.MainNotions.S.muS A B) =
      ∫⁻ p, φ (Cm g p) ∂((A.prod B).prod (A'.prod B)) := by
  have hm := meas_mulM (k := k) (r := r)
  have hi := meas_invM (k := k) (r := r)
  have hT := meas_Tm g
  have hmu : ∀ X Y : Measure (Mt k r), Formalism.MainNotions.S.muS X Y = (X.prod Y).map mulM := fun _ _ => rfl
  rw [hmu, hmu]
  have step1 : ∀ s, ∫⁻ s', φ (Tm g (s, s')) ∂((A'.prod B).map mulM) =
      ∫⁻ y, φ (Tm g (s, mulM y)) ∂(A'.prod B) := fun s =>
    lintegral_map (hφ.comp (hT.comp (measurable_const.prodMk measurable_id))) hm
  rw [lintegral_congr step1]
  have hH : Measurable fun s => ∫⁻ y, φ (Tm g (s, mulM y)) ∂(A'.prod B) :=
    Measurable.lintegral_prod_right' (f := fun q : Mt k r × (Mt k r × Mt k r) => φ (Tm g (q.1, mulM q.2)))
      (hφ.comp (hT.comp (measurable_fst.prodMk (hm.comp measurable_snd))))
  rw [lintegral_map hH hm]
  have hF : Measurable fun p : (Mt k r × Mt k r) × (Mt k r × Mt k r) => φ (Tm g (mulM p.1, mulM p.2)) :=
    hφ.comp (hT.comp ((hm.comp measurable_fst).prodMk (hm.comp measurable_snd)))
  rw [← lintegral_prod _ hF.aemeasurable]
  have hpt : ∀ p : (Mt k r × Mt k r) × (Mt k r × Mt k r),
      Tm g (mulM p.1, mulM p.2) = Cm g (Prod.map id (Prod.map invM invM) p) := by
    intro p
    show (Matrix.of p.1.1 * Matrix.of p.1.2 * Matrix.of g * (Matrix.of p.2.1 * Matrix.of p.2.2)⁻¹ : Mat k r) =
      Matrix.of p.1.1 * Matrix.of p.1.2 * Matrix.of g * (Matrix.of p.2.2)⁻¹ * (Matrix.of p.2.1)⁻¹
    rw [Matrix.mul_inv_rev]
    exact (mul_assoc _ _ _).symm
  simp only [hpt]
  have h2 : (A'.prod B).map (Prod.map invM invM) = A'.prod B := by
    rw [← Measure.map_prod_map A' B hi hi, hA', hB]
  have hP : ((A.prod B).prod (A'.prod B)).map (Prod.map id (Prod.map invM invM)) = (A.prod B).prod (A'.prod B) := by
    rw [← Measure.map_prod_map _ _ measurable_id (hi.prodMap hi), Measure.map_id, h2]
  refine (lintegral_map (f := φ ∘ Cm g) (hφ.comp (meas_Cm g)) (measurable_id.prodMap (hi.prodMap hi))).symm.trans ?_
  rw [hP]
  rfl

theorem src_eq (A B A' : Measure (Mt k r)) [SFinite A] [SFinite B] [SFinite A']
    (hA : A.map invM = A) (hB : B.map invM = B) (g : Mat k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ p, φ (sgs p g) ∂((A.prod B).prod (A'.prod B)) = ∫⁻ p, φ (Cm g p) ∂((A.prod B).prod (A'.prod B)) := by
  have hi := meas_invM (k := k) (r := r)
  have hpt : ∀ p : SS k r, (sgs p g : Mt k r) = Cm g (Prod.map (Prod.map invM invM) id p) := fun _ => rfl
  simp only [hpt]
  have h1 : (A.prod B).map (Prod.map invM invM) = A.prod B := by
    rw [← Measure.map_prod_map A B hi hi, hA, hB]
  have hP : ((A.prod B).prod (A'.prod B)).map (Prod.map (Prod.map invM invM) id) = (A.prod B).prod (A'.prod B) := by
    rw [← Measure.map_prod_map _ _ (hi.prodMap hi) measurable_id, Measure.map_id, h1]
  refine (lintegral_map (f := φ ∘ Cm g) (hφ.comp (meas_Cm g)) ((hi.prodMap hi).prodMap measurable_id)).symm.trans ?_
  rw [hP]
  rfl

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.HaarTranslationMeasurability

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 HaarTranslationMeasurability

theorem hpkEx_holds : HpkEx := by
  intro k r z z' hk hz hz' hT hT' μ μW μW' μN hμ hW hW' hN μsec hsec
  obtain ⟨μG0, hG0⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨μW0, hW0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  obtain ⟨μW0', hW0'⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z' hz' hT'
  obtain ⟨μN0, hN0⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  have hD : IsMeasData k r z z' μsec μG0 μW0 μN0 μW0' := ⟨hk, hz, hz', hT, hT', hG0, hW0, hN0, hW0', hsec⟩
  obtain ⟨C, hC, hInt⟩ := Formalism.FourierDecayAlt.P.integration_formula_constant k r z z' μsec μG0 μW0 μN0 μW0' hD
  have cG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have cW := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have cW' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  have cN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  obtain ⟨a, ha0, hat, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cG hG0 hμ
  obtain ⟨b, hb0, hbt, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cW hW0 hW
  obtain ⟨b', hb0', hbt', rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cW' hW0' hW'
  obtain ⟨d, hd0, hdt, rfl⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant cN hN0 hN
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW0
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hW0'
  haveI := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hN0
  have iW := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μW0 cW hW0
  have iW' := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μW0' cW' hW0'
  have iN := Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μN0 cN hN0
  have jW' : (b' • μW0').map invM = b' • μW0' := by rw [Measure.map_smul, iW']
  have jN : (d • μN0).map invM = d • μN0 := by rw [Measure.map_smul, iN]
  set κ : ℝ≥0∞ := b * d * (b' * d) with hκ
  have hκ0 : κ ≠ 0 := by simp [hκ, hb0, hd0, hb0']
  have hκt : κ ≠ ⊤ := by simp [hκ, ENNReal.mul_eq_top, hbt, hdt, hbt']
  have key : ∀ (g : Mat k r) (φ : Mt k r → ℝ≥0∞), Measurable φ →
      ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * g * (Matrix.of s')⁻¹) i j)
          ∂(Formalism.MainNotions.S.muS (b' • μW0') (d • μN0)) ∂(Formalism.MainNotions.S.muS (b • μW0) (d • μN0)) =
        κ * ∫⁻ p, φ (sgs p g) ∂((μW0.prod μN0).prod (μW0'.prod μN0)) := by
    intro g φ hφ
    have := tgt_eq (b • μW0) (d • μN0) (b' • μW0') jN jW' g φ hφ
    refine this.trans ?_
    rw [src_eq μW0 μN0 μW0' iW iN g φ hφ]
    simp only [Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure, smul_eq_mul, hκ]
    ring
  have hne : a * (C : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top hat ENNReal.coe_ne_top
  have hne0 : a * (C : ℝ≥0∞) ≠ 0 := mul_ne_zero ha0 (by exact_mod_cast hC.ne')
  refine ⟨(a * C / κ).toReal, ENNReal.toReal_pos (by simp [ENNReal.div_eq_zero_iff, hne0, hκt])
    (ENNReal.div_lt_top hne hκ0).ne, fun φ hφ => ?_⟩
  rw [ENNReal.ofReal_toReal (ENNReal.div_lt_top hne hκ0).ne, lintegral_smul_measure, hInt φ hφ, smul_eq_mul]
  simp_rw [key _ φ hφ]
  have hc : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
      (κ * ∫⁻ p, φ (sgs p (bigCell k r q.1 (μsec q.2))) ∂((μW0.prod μN0).prod (μW0'.prod μN0))) =
      κ * (ENNReal.ofReal (bcWeight k r (Tz k r z) (Tz k r z') q) *
        ∫⁻ p, φ (sgs p (bigCell k r q.1 (μsec q.2))) ∂((μW0.prod μN0).prod (μW0'.prod μN0))) := fun q => by ring
  simp_rw [hc]
  rw [lintegral_const_mul' _ _ hκt, ← mul_assoc, ← mul_assoc, ENNReal.div_mul_cancel hκ0 hκt]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

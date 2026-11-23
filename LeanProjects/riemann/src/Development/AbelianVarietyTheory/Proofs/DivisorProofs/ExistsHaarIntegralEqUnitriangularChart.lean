import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UpperTriangularPreservesDiagonalIff
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFLtTopOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal Matrix

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def baseGL (X : Data E r) (τ : X.Ψ) : GL (Fin r) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (mat (baseFr X) τ) (PeterssonCompare.det_baseFr X τ)

theorem val_baseGL (X : Data E r) (τ : X.Ψ) : (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) = mat (baseFr X) τ := rfl

omit [NumberField E] [IsCMField E] in

theorem gram_mul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (A g : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (A * g) = gᵀ * gram τ G A * g.map (starRingEnd ℂ) := by
  rw [UnitaryFrames.gram_eq_mul, UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in

theorem isometry_iff_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (n : Matrix (Fin r) (Fin r) ℂ)
    (P : GL (Fin r) ℂ) :
    (∀ u w, hermC τ G (n *ᵥ u) (n *ᵥ w) = hermC τ G u w) ↔
      gram τ G (n * (P : Matrix (Fin r) (Fin r) ℂ)) = gram τ G P := by
  constructor
  · intro h
    ext a b
    simp only [gram, Matrix.of_apply, UnitaryFrames.col_mul', h]
  · intro h u w
    obtain ⟨u', rfl⟩ : ∃ u', u = (P : Matrix (Fin r) (Fin r) ℂ) *ᵥ u' :=
      ⟨((P⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ u, by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
    obtain ⟨w', rfl⟩ : ∃ w', w = (P : Matrix (Fin r) (Fin r) ℂ) *ᵥ w' :=
      ⟨((P⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *ᵥ w, by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, UnitaryFrames.hermC_mulVec, UnitaryFrames.hermC_mulVec, h]

def toIso (X : Data E r) (g : RealGrp X) : UnitaryFrames.unitarySubgroup X :=
  ⟨fun τ => baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹, by
    intro τ
    refine (isometry_iff_gram τ.1 X.Gm _ (baseGL X τ)).2 ?_
    rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul, gram_mul_right, val_baseGL, baseFr_mem X τ]
    exact (g τ).2⟩

def ofIso (X : Data E r) (h : UnitaryFrames.unitarySubgroup X) : RealGrp X :=
  fun τ => ⟨(baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ, by
    have hu : gram τ.1 X.Gm (((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        (baseGL X τ : Matrix (Fin r) (Fin r) ℂ)) = gram τ.1 X.Gm (baseGL X τ) :=
      (isometry_iff_gram τ.1 X.Gm _ (baseGL X τ)).1 (h.2 τ)
    have e : ((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) =
        (baseGL X τ : Matrix (Fin r) (Fin r) ℂ) *
          (((baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [e, gram_mul_right, val_baseGL, baseFr_mem X τ] at hu
    exact hu⟩

def isoEquiv (X : Data E r) : RealGrp X ≃ₜ* UnitaryFrames.unitarySubgroup X where
  toFun := toIso X
  invFun := ofIso X
  left_inv g := by
    funext τ
    apply Subtype.ext
    show (baseGL X τ)⁻¹ * (baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹) * baseGL X τ = _
    group
  right_inv h := by
    apply Subtype.ext
    funext τ
    show baseGL X τ * ((baseGL X τ)⁻¹ * (h : X.Ψ → GL (Fin r) ℂ) τ * baseGL X τ) * (baseGL X τ)⁻¹ = _
    group
  map_mul' g g' := by
    apply Subtype.ext
    funext τ
    show baseGL X τ * (((g * g') τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹ =
      (baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹) *
        (baseGL X τ * ((g' τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹)
    simp only [Pi.mul_apply, Subgroup.coe_mul]
    group
  continuous_toFun := by
    refine continuous_induced_rng.2 (continuous_pi fun τ => ?_)
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply τ))).mul continuous_const
  continuous_invFun := by
    refine continuous_pi fun τ => continuous_induced_rng.2 ?_
    exact (continuous_const.mul ((continuous_apply τ).comp continuous_subtype_val)).mul continuous_const

theorem frameOf_eq_lmulC (X : Data E r) (g : RealGrp X) :
    frameOf X g = X.lmulC (fun τ => (((toIso X g : UnitaryFrames.unitarySubgroup X) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) (baseFr X) := by
  funext τ
  have key : mat (frameOf X g) τ = mat (X.lmulC (fun τ => (((toIso X g : UnitaryFrames.unitarySubgroup X) :
      X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) (baseFr X)) τ := by
    rw [PeterssonCompare.mat_frameOf, show ∀ (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r),
    mat (X.lmulC n x) τ = n τ * mat x τ from fun _ _ => rfl, ← val_baseGL]
    show _ = ((baseGL X τ * ((g τ : Upq r X.p0) : GL (Fin r) ℂ) * (baseGL X τ)⁻¹ : GL (Fin r) ℂ) :
    Matrix (Fin r) (Fin r) ℂ) * _
    rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  exact key

theorem muF_univ_ne_zero (X : Data E r) {x0 : Frame X.Ψ r} (h : IsOrth X x0) : muF X x0 Set.univ ≠ 0 := by
  have hO := OntoB.isOpen_OmF X x0
  unfold muF
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  intro h0
  have hm : AEMeasurable (fun z => ENNReal.ofReal (densF X x0 z)) (volume.restrict (OmF X x0)) :=
    (OntoB.densF_continuousOn.aemeasurable hO.measurableSet).ennreal_ofReal
  rw [lintegral_eq_zero_iff' hm] at h0
  have h1 : ∀ᵐ z ∂(volume.restrict (OmF X x0)), False := by
    filter_upwards [h0, ae_restrict_mem hO.measurableSet] with z hz hz'
    have := OntoB.densF_pos hz'
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hz
    linarith
  rw [ae_iff] at h1
  simp only [not_false_eq_true, Set.setOf_true, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter] at h1
  exact (hO.measure_pos volume ⟨0, IW.zero_mem_OmF X x0 h⟩).ne' h1

theorem exists_haarChart (X : Data E r) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ HaarChart X c := by
  classical
  set H := UnitaryFrames.unitarySubgroup X with hHdef
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  have hHm : ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ) := fun _ => Iff.rfl
  obtain ⟨hLC, hSC, -⟩ := UnitaryFrames.unitary_group_frames.2 r X H hHm
  haveI := hLC
  haveI := hSC
  have hx0 : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
  obtain ⟨ν, hνl, hνf, hν⟩ := UnitaryInvMeasure.invMeas FrameMeasureClosed.measure_statements.2.1
    GramSchmidtCont.exists_continuous_gramSchmidt isOrth_rmul_iff_unitary_diagonal
    (SatFin.muF_sat_lt_top FrameMeasureClosed.measure_statements.2.1)
    UnitaryFrames.unitary_group_frames.2 r X H hHm (baseFr X) hx0
  haveI := hνl
  haveI := hνf
  haveI : (haarR X).IsHaarMeasure := by unfold haarR; infer_instance
  set e := isoEquiv X
  set μ : Measure H := (haarR X).map e with hμdef
  haveI : μ.IsHaarMeasure := e.isHaarMeasure_map (haarR X)
  have hs := Measure.isMulLeftInvariant_eq_smul ν μ
  set s := ν.haarScalarFactor μ
  set L : H → Frame X.Ψ r := fun h =>
    X.lmulC (fun τ => ((h : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) (baseFr X)

  have hR : ∀ F : H → ℝ≥0∞, ∫⁻ g, F (e g) ∂haarR X = ∫⁻ h, F h ∂μ := by
    intro F
    have := lintegral_map_equiv F (e.toHomeomorph.toMeasurableEquiv) (μ := haarR X)
    exact this.symm
  have hs0 : s ≠ 0 := by
    intro h0
    have h1 := hν (fun _ => 1) measurable_const (fun _ _ _ _ => rfl)
    simp only [lintegral_const, one_mul] at h1
    rw [hs, h0, zero_smul, Measure.coe_zero, Pi.zero_apply] at h1
    exact muF_univ_ne_zero X hx0 h1.symm
  refine ⟨((s : ℝ≥0∞))⁻¹, ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hs0), fun φ hφ hφb => ?_⟩
  have h1 := hν φ hφ hφb
  rw [hs, lintegral_smul_measure] at h1
  have h2 : ∫⁻ g, φ (frameOf X g) ∂haarR X = ∫⁻ h, φ (L h) ∂μ := by
    rw [← hR]
    refine lintegral_congr fun g => ?_
    rw [frameOf_eq_lmulC]
    rfl
  rw [h2, ← h1, ENNReal.smul_def, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hs0)
    ENNReal.coe_ne_top, one_mul]

end

end GlobalTheory.FlagQuotHaar

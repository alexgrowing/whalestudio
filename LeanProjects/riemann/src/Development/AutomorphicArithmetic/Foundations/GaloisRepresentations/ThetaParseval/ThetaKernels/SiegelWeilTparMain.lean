import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.TThetaSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem frameData_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ t0 : GL (Fin d.n) E,
    incM F d.b.1 = Matrix.fromCols (incM F d.b.1.toCols₁) (incM F d.b.1.toCols₂) ∧
    incM F d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 ∧
    ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1.toCols₂).map (cA σ) = 1 ∧
    incM F t0.1 * incM F (t0⁻¹).1 = 1 := by
  obtain ⟨t0, ht0'⟩ := d.ok.frame.2
  have ht0 : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * t0.1 := ht0'
  have hBx : incM F d.b.1.toCols₁ =
      (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 := by
    rw [ht0, incM_mul, incM_diagCols]
  refine ⟨t0, incM_fromCols _, hBx, ?_, ?_⟩
  · rw [← hBx]; exact frame_xy_A d.ok.frame
  · rw [← incM_mul, Units.mul_inv, incM_one]
theorem tPar_k : _root_.PositivityTheory.SiegelWeilFormula.TPar_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, hB, hBx, hf, hT⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  have mem : ∀ w, d.dd.rho d.B.ψ w Φ ∈ schA F d.κ := fun w => GlobalTheory.HeisSchA.schr_mem_schA _ hψ _ Φ hΦ
  refine ⟨fun x β hx X => ?_, fun x t u hx X => ?_, fun g X => ?_⟩
  · have h1 := inFrame_mul hx
    have h2 := inv_mul_frame h1 (N' := Matrix.fromBlocks 1 (-β) 0 1)
      (by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one])
    rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
    replace h1 := Matrix.fromCols_inj h1
    replace h2 := Matrix.fromCols_inj h2
    rw [hBx] at h1 h2
    have hpar : IsPar x 1 := by
      have e := par_of hT (show mat2 x * ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) *
          incM F t0.1) = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 * 1 by
        rw [h1.1]; simp)
      rw [Matrix.mul_one, hT] at e
      unfold IsPar
      rw [Units.val_one]
      exact e
    have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 x⁻¹)ᵀ = -(X * βᵀ * (incM F t0.1)ᵀ) *
        (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ + X * (incM F d.b.1.toCols₂)ᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, h2.2]
      simp [Matrix.transpose_mul, Matrix.transpose_add, Matrix.mul_add, Matrix.mul_assoc, Matrix.transpose_neg]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
    rw [l_rho_om h x _ hΦ, l_om_par h hpar (mem _), key, l_shift h hψ _ _ hΦ, symp_N _ _ _ _ _ _ hf]
    simp
  · have h1 := inFrame_mul hx
    have h2 := inv_mul_frame h1 (N' := Matrix.fromBlocks (t⁻¹ : GL (Fin d.n) (AE F E)).1 0 0 (u⁻¹ : GL (Fin d.n) (AE F E)).1)
      (by simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one])
    rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
    replace h1 := Matrix.fromCols_inj h1
    replace h2 := Matrix.fromCols_inj h2
    rw [hBx] at h1 h2
    obtain ⟨G0, hG0⟩ : ∃ G0 : GL (Fin d.n) (AE F E), G0 = Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) t0 :=
      ⟨_, rfl⟩
    have g1 : (G0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F t0.1 := by
      rw [hG0]; rfl
    have g2 : ((G0⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = incM F (t0⁻¹).1 := by
      rw [hG0, ← map_inv]; rfl
    have hpar : IsPar x (G0 * t * G0⁻¹) := by
      have e := par_of hT (show mat2 x * ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) *
          incM F t0.1) = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)) * incM F t0.1 * t.1 by
        rw [h1.1]; simp)
      unfold IsPar
      rw [Units.val_mul, Units.val_mul, g1, g2]
      exact e
    have hdet : Matrix.GeneralLinearGroup.det (G0 * t * G0⁻¹) = Matrix.GeneralLinearGroup.det t := by
      rw [map_mul, map_mul, map_inv]
      exact mul_inv_cancel_comm _ _
    have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 x⁻¹)ᵀ = X * (u⁻¹).1ᵀ * (incM F d.b.1.toCols₂)ᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, h2.2]
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [l_rho_om h x _ hΦ, l_om_par h hpar (mem _), hdet, key]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T]
    rw [l_rho_S h hψ g _ hΦ, Matrix.mul_assoc]
def TThetaSum_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ ∈ d.sch, HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => d.T Φ (incM F X)) (thetaSum F Φ)
theorem tThetaSum_k : _root_.PositivityTheory.SiegelWeilFormula.Tpar.TThetaSum_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, ht0'⟩ := d.ok.frame.2
  have ht0 : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * t0.1 := ht0'
  obtain ⟨Am, hAm⟩ : ∃ Am : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E, Am = Matrix.fromRows 1 (-1) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (d.b⁻¹).1 * Am := ⟨_, rfl⟩
  have hA : Am = d.b.1.toCols₁ * M.toRows₁ + d.b.1.toCols₂ * M.toRows₂ := by
    rw [← Matrix.fromCols_mul_fromRows, Matrix.fromCols_toCols, Matrix.fromRows_toRows, hM, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]
  have hinj : ∀ v, M.toRows₂ *ᵥ v = 0 → v = 0 := by
    intro v hv
    have e1 : Am *ᵥ v = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) *ᵥ (t0.1 *ᵥ (M.toRows₁ *ᵥ v)) := by
      rw [hA, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero, ht0,
        ← Matrix.mulVec_mulVec]
    funext i
    have a1 := congrFun e1 (Sum.inl i)
    have a2 := congrFun e1 (Sum.inr i)
    simp [hAm, diagCols, Matrix.fromRows_mulVec, Matrix.neg_mulVec] at a1 a2
    have : (2 : E) * v i = 0 := by linear_combination a1 - a2
    simpa using this
  have hu : IsUnit M.toRows₂.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.mulVec_injective_iff_isUnit.1 fun v w e => sub_eq_zero.1 (hinj _ (by rw [Matrix.mulVec_sub, e, sub_self])))
  let e : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E :=
    { toFun := fun y => y * M.toRows₂ᵀ
      invFun := fun X => X * (M.toRows₂)⁻¹ᵀ
      left_inv := fun y => by
        simp only
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hu, Matrix.transpose_one, Matrix.mul_one]
      right_inv := fun X => by
        simp only
        rw [Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one, Matrix.mul_one] }
  have hterm : ∀ y : Matrix (Fin d.m) (Fin d.n) E,
      d.l (d.dd.rho d.B.ψ (incM F (Matrix.fromCols y (-y))) Φ) = d.T Φ (incM F (e y)) := by
    intro y
    have hy : Matrix.fromCols y (-y) = y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E)ᵀ + y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ := by
      have : Matrix.fromCols y (-y) = y * Amᵀ := by simp [hAm, Matrix.transpose_fromRows, Matrix.mul_fromCols]
      rw [this, hA, ht0]
      simp [Matrix.transpose_add, Matrix.transpose_mul, Matrix.mul_add, Matrix.mul_assoc]
    have ea : incM F (y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E)ᵀ) = incM F (y * M.toRows₁ᵀ * t0.1ᵀ) *
        (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ := by
      simp only [incM_mul, incM_transpose, incM_diagCols]
    have ec : incM F (y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ) = incM F (y * M.toRows₂ᵀ) * (incM F d.b.1.toCols₂)ᵀ := by
      simp only [incM_mul, incM_transpose]
    have hr := psi_rat h hψ (y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E)ᵀ) (y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ)
    rw [ea, ec] at hr
    rw [hy, incM_add, ea, ec, l_shift h hψ _ _ hΦ, hr, one_mul]
    rfl
  have hs := h.theta Φ hΦ
  rw [show (fun y : Matrix (Fin d.m) (Fin d.n) E => d.l (d.dd.rho d.B.ψ (incM F (Matrix.fromCols y (-y))) Φ)) =
      (fun X => d.T Φ (incM F X)) ∘ e from funext hterm] at hs
  exact (Equiv.hasSum_iff e).1 hs
theorem tTheta_of_k
    (h2 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ),
      ∀ Φ ∈ d.sch, ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ)) : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k :=
  fun F E _ _ _ _ _ σ d Φ hΦ => ⟨_root_.PositivityTheory.SiegelWeilFormula.Tpar.tThetaSum_k F E σ d Φ hΦ, h2 F E σ d Φ hΦ⟩
end PositivityTheory.SiegelWeilFormula.Tpar
end
end

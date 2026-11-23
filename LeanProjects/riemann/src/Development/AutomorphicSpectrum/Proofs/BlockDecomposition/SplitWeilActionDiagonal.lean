import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariant
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitDiag

open Ad3.K.GL2LocalData
open GlobalTheory.CompanionTheory.WeilSplit (norm_pair)
open GlobalTheory.CompanionTheory.SplitGauss (trace_swap)

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem map_dil (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) :
    Measure.map (Prod.map (fun x : F => s * x) (fun x : F => x)) (muS χ) = (modulus s)⁻¹ • muS χ := by
  have e1 : MeasurableEmbedding (fun x : F => s * x) := (Homeomorph.mulLeft₀ s hs).measurableEmbedding
  rw [← Measure.map_prod_map _ _ e1.measurable measurable_id', map_mul_left_eq_smul _ hs,
    Measure.prod_smul_left]
  simp

theorem integral_dil (χ : AddChar F Circle) {s : F} (hs : s ≠ 0) (G : F × F → ℂ) :
    ∫ u, G u ∂muS χ = ((modulus s : ℝ) : ℂ) * ∫ u, G (s * u.1, u.2) ∂muS χ := by
  have e1 : MeasurableEmbedding (fun x : F => s * x) := (Homeomorph.mulLeft₀ s hs).measurableEmbedding
  have h := (e1.prodMap MeasurableEmbedding.id).integral_map (μ := muS χ) G
  have hm : ((modulus s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hs
  have h' : ((modulus s : ℝ) : ℂ)⁻¹ * ∫ u, G u ∂muS χ = ∫ u, G (s * u.1, u.2) ∂muS χ := by
    have e2 : Measure.map (Prod.map (fun x : F => s * x) id) (muS χ) = (modulus s)⁻¹ • muS χ :=
      map_dil χ hs
    rw [e2, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul] at h
    push_cast at h
    exact h
  rw [← h', mul_inv_cancel_left₀ hm]

theorem nsg_pair {y : F} (hy : y ≠ 0) : nsg (F × F) y = 1 := by
  unfold nsg
  rw [if_pos]
  refine ⟨⟨(y, 1), (y⁻¹, 1), ?_, ?_⟩, ?_⟩
  · ext <;> simp [hy]
  · ext <;> simp [hy]
  · simp [norm_pair]

theorem mp_mul' (a b : Fˣ) (s : ℂ) : mp (a * b) s = mp a s * mp b s := by
  simp only [mp, Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) s

theorem rW_dil (χ : AddChar F Circle) (a b c d : F) (A : Fˣ) (f : F × F → ℂ) (x : F × F) :
    rW χ swapE (muS χ) 1 a ((A : F) * b) (c / A) d (fun y => f (y * ((A : F), 1))) x =
      rW χ swapE (muS χ) 1 a b c d f ((A : F) * x.1, x.2) := by
  obtain ⟨x1, x2⟩ := x
  have hA : (A : F) ≠ 0 := A.ne_zero
  by_cases hc : c = 0
  · have hc' : c / (A : F) = 0 := by simp [hc]
    simp only [rW, if_pos hc, if_pos hc', norm_pair]
    have e1 : a * ((A : F) * b) * (x1 * x2) = a * b * ((A : F) * x1 * x2) := by ring
    have e2 : algebraMap F (F × F) a * (x1, x2) * ((A : F), 1) =
        algebraMap F (F × F) a * ((A : F) * x1, x2) := by
      ext <;> simp
      ring
    rw [e1, e2]
  · have hc' : c / (A : F) ≠ 0 := div_ne_zero hc hA
    simp only [rW, if_neg hc, if_neg hc', norm_pair, trace_swap,
      nsg_pair (neg_ne_zero.2 hc), nsg_pair (neg_ne_zero.2 hc')]
    have hm : (((modulus (c / (A : F)) : ℝ)⁻¹ : ℝ) : ℂ) =
        (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * ((modulus (A : F) : ℝ) : ℂ) := by
      rw [div_eq_mul_inv, modulus_mul, modulus_inv]
      push_cast
      rw [mul_inv, inv_inv]
    set G : F × F → ℂ := fun v =>
      (χ ((a * ((A : F) * x1 * x2) + d * (v.1 * v.2) - (v.1 * x2 + v.2 * ((A : F) * x1))) / c) : ℂ) * f v
      with hG
    rw [integral_dil χ hA G, hm]
    have hI : ∫ u : F × F, (χ ((a * (x1 * x2) + d * (u.1 * u.2) - (u.1 * x2 + u.2 * x1)) / (c / (A : F))) : ℂ) *
          f (u * ((A : F), 1)) ∂muS χ = ∫ u, G ((A : F) * u.1, u.2) ∂muS χ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      have e1 : (a * (x1 * x2) + d * (u.1 * u.2) - (u.1 * x2 + u.2 * x1)) / (c / (A : F)) =
          (a * ((A : F) * x1 * x2) + d * ((A : F) * u.1 * u.2) -
            ((A : F) * u.1 * x2 + u.2 * ((A : F) * x1))) / c := by
        field_simp
      have e2 : u * (((A : F), 1) : F × F) = ((A : F) * u.1, u.2) := by
        ext <;> simp [mul_comm]
      simp only [hG, e1, e2]
    rw [hI]
    ring

end GlobalTheory.CompanionTheory.SplitDiag

theorem GlobalTheory.CompanionTheory.SplitDiag.piS_diag : GL2LocalData.ForES fun F _ _ _ _ _ _ _ χ => ∀ (c₁ : Fˣ →* ℂˣ) (Φ : F × F → ℂ), IsLocallyConstant Φ → HasCompactSupport Φ →
  ∀ (a : Fˣ) (g : GL (Fin 2) F) (x : F × F),
    GL2LocalData.piS χ c₁ (dg2 a 1 * g) Φ x = ((c₁ a : ℂˣ) : ℂ) * mp a (1 / 2) * GL2LocalData.piS χ c₁ g Φ ((a : F) * x.1, x.2) := by
  intro F _ _ _ _ _ _ _ χ _ _ c₁ Φ _ _ a g x
  have hv : ((dg2 a 1 * g).val).det = (a : F) * (g.val).det := by
    have h0 : ((dg2 a 1 : GL (Fin 2) F).val).det = (a : F) := by
      simp [dg2, Matrix.det_fin_two]
    rw [Units.val_mul, Matrix.det_mul, h0]
  have hd : Matrix.GeneralLinearGroup.det (dg2 a 1 * g) = a * Matrix.GeneralLinearGroup.det g := by
    ext
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using hv
  have hD : (g.val).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det g).ne_zero
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have e00 : (dg2 a 1 * g).val 0 0 = (a : F) * g.val 0 0 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (dg2 a 1 * g).val 0 1 = (a : F) * g.val 0 1 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (dg2 a 1 * g).val 1 0 = g.val 1 0 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (dg2 a 1 * g).val 1 1 = g.val 1 1 := by
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have hA : (a : F) ≠ 0 := a.ne_zero
  have h1 : (a : F) * g.val 0 0 / ((a : F) * (g.val).det) = g.val 0 0 / (g.val).det := by
    field_simp
  have h2 : g.val 1 0 / ((a : F) * (g.val).det) = g.val 1 0 / (g.val).det / (a : F) := by
    field_simp
  have key := GlobalTheory.CompanionTheory.SplitDiag.rW_dil χ (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det)
    (g.val 1 1) a (fun y => Φ (y * ((g.val).det, 1))) x
  have hf : (fun y : F × F => Φ (y * ((a : F) * (g.val).det, 1))) =
      fun y => Φ (y * ((a : F), 1) * ((g.val).det, 1)) := by
    funext y
    congr 1
    ext <;> simp [mul_assoc]
  simp only [GL2LocalData.piS]
  rw [hd, hv, e00, e01, e10, e11, h1, h2, hf, key, map_mul, Units.val_mul, GlobalTheory.CompanionTheory.SplitDiag.mp_mul']
  ring

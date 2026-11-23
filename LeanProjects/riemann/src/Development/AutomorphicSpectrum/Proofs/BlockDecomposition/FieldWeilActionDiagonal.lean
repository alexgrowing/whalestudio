import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalThetaCentralCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NsgDivNorm
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.PieDiag

theorem piE_diag : GL2LocalData.ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (c : Eˣ →* ℂˣ), ∀ Φ ∈ GL2LocalData.SBc F E c, ∀ (t : Eˣ) (a : Fˣ),
  (a : F) = Algebra.norm F (t : E) → ∀ (g : GL (Fin 2) F) (x : E),
    GL2LocalData.piE E χ σ η c (dg2 a 1 * g) Φ x = ((c t : ℂˣ) : ℂ) * mp a (1 / 2) * GL2LocalData.piE E χ σ η c g Φ (x * t) := by
  intro F _ _ _ _ _ _ _ χ hχc hχ E _ _ _ _ _ _ _ hd hc σ hσ η hη c Φ hΦ t a hat g x
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  have hdet : ((dg2 a 1 * g).val).det = (a : F) * (g.val).det := by
    show ((dg2 a 1).val * g.val).det = _
    rw [Matrix.det_mul]
    congr 1
    simp [dg2, Matrix.det_fin_two]
  by_cases h : ∃ s : Eˣ, Algebra.norm F (s : E) = (g.val).det
  swap
  · have h' : ¬ ∃ s : Eˣ, Algebra.norm F (s : E) = ((dg2 a 1 * g).val).det := by
      rintro ⟨s, hs⟩
      refine h ⟨t⁻¹ * s, ?_⟩
      have e : (a : F) * Algebra.norm F ((t⁻¹ * s : Eˣ) : E) = (a : F) * (g.val).det := by
        rw [← hdet, ← hs, hat, ← map_mul, ← Units.val_mul, mul_inv_cancel_left]
      exact mul_left_cancel₀ ha0 e
    show GL2LocalData.piG _ _ _ _ _ _ _ _ = _ * GL2LocalData.piG _ _ _ _ _ _ _ _
    rw [GL2LocalData.piG, GL2LocalData.piG, dif_neg h, dif_neg h', mul_zero]
  obtain ⟨s, hs⟩ := h
  have hN' : Algebra.norm F ((s * t : Eˣ) : E) = ((dg2 a 1 * g).val).det := by
    rw [Units.val_mul, map_mul, hs, ← hat, hdet, mul_comm]
  have L := GlobalTheory.CompanionTheory.CenThetaNs.piG_choice F χ hχc hχ E hd hc σ hσ η hη c Φ hΦ (dg2 a 1 * g) (s * t) x hN'
  have R := GlobalTheory.CompanionTheory.CenThetaNs.piG_choice F χ hχc hχ E hd hc σ hσ η hη c Φ hΦ g s (x * t) hs
  rw [L, R]
  have hD : (g.val).det ≠ 0 := by
    rw [← hs]
    exact (s.isUnit.map (Algebra.norm F : E →* F)).ne_zero
  have e00 : (dg2 a 1 * g).val 0 0 = (a : F) * g.val 0 0 := by
    show ((dg2 a 1).val * g.val) 0 0 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (dg2 a 1 * g).val 0 1 = (a : F) * g.val 0 1 := by
    show ((dg2 a 1).val * g.val) 0 1 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (dg2 a 1 * g).val 1 0 = g.val 1 0 := by
    show ((dg2 a 1).val * g.val) 1 0 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (dg2 a 1 * g).val 1 1 = g.val 1 1 := by
    show ((dg2 a 1).val * g.val) 1 1 = _
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e00, e01, e10, e11, hdet]
  set D : F := (g.val).det with hDdef
  set g1 : Matrix (Fin 2) (Fin 2) F := !![g.val 0 0 / D, g.val 0 1; g.val 1 0 / D, g.val 1 1] with hg1def
  have hg1 : g1.det = 1 := by
    have : D = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 := by
      rw [hDdef, Matrix.det_fin_two]
    rw [hg1def, Matrix.det_fin_two_of]
    field_simp
    exact this.symm
  have hΨ : (fun y => Φ (y * (s : E))) ∈ GL2LocalData.SBE E := by
    refine ⟨hΦ.1.comp_continuous (continuous_id.mul continuous_const), ?_⟩
    exact hΦ.2.1.comp_homeomorph (Homeomorph.mulRight₀ (s : E) (Units.ne_zero _))
  have hw := congrFun (GlobalTheory.CompanionTheory.WeilDilation.wDiagT F χ hχc hχ E hd hc σ hσ η hη g1 hg1 t _ hΨ) x
  have hfun : (fun y => Φ (y * ((s * t : Eˣ) : E))) = fun y => (fun y => Φ (y * (s : E))) (y * (t : E)) := by
    funext y
    show Φ _ = Φ _
    congr 1
    rw [Units.val_mul]
    ring
  have hl : GL2LocalData.rW χ σ (GL2LocalData.muE E χ) (GL2LocalData.lamE E χ η) ((a : F) * g.val 0 0 / ((a : F) * D)) ((a : F) * g.val 0 1)
      (g.val 1 0 / ((a : F) * D)) (g.val 1 1) (fun y => Φ (y * ((s * t : Eˣ) : E))) x =
      GL2LocalData.rW χ σ (GL2LocalData.muE E χ) (GL2LocalData.lamE E χ η) (g.val 0 0 / D) (g.val 0 1) (g.val 1 0 / D) (g.val 1 1)
        (fun y => Φ (y * (s : E))) (x * (t : E)) := by
    have f00 : GL2LocalData.cjA (Algebra.norm F (t : E)) g1 0 0 = (a : F) * g.val 0 0 / ((a : F) * D) := by
      simp [GL2LocalData.cjA, hg1def]
      field_simp
    have f01 : GL2LocalData.cjA (Algebra.norm F (t : E)) g1 0 1 = (a : F) * g.val 0 1 := by
      simp [GL2LocalData.cjA, hg1def, hat]
    have f10 : GL2LocalData.cjA (Algebra.norm F (t : E)) g1 1 0 = g.val 1 0 / ((a : F) * D) := by
      simp [GL2LocalData.cjA, hg1def, hat]
      field_simp
    have f11 : GL2LocalData.cjA (Algebra.norm F (t : E)) g1 1 1 = g.val 1 1 := by
      simp [GL2LocalData.cjA, hg1def]
    have hw' : GL2LocalData.rW χ σ (GL2LocalData.muE E χ) (GL2LocalData.lamE E χ η) (g.val 0 0 / D) (g.val 0 1) (g.val 1 0 / D) (g.val 1 1)
        (fun y => Φ (y * (s : E))) (x * (t : E)) =
        GL2LocalData.rW χ σ (GL2LocalData.muE E χ) (GL2LocalData.lamE E χ η) (GL2LocalData.cjA (Algebra.norm F (t : E)) g1 0 0)
          (GL2LocalData.cjA (Algebra.norm F (t : E)) g1 0 1) (GL2LocalData.cjA (Algebra.norm F (t : E)) g1 1 0)
          (GL2LocalData.cjA (Algebra.norm F (t : E)) g1 1 1)
          (fun y => (fun y => Φ (y * (s : E))) (y * (t : E))) x := hw
    rw [hw', f00, f01, f10, f11, hfun]
  rw [hl, map_mul, Units.val_mul]
  have hmod : (((modulus ((a : F) * D) : ℝ)) : ℂ) ^ (1 / 2 : ℂ) =
      mp a (1 / 2) * (((modulus D : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [modulus_mul, mp]
    push_cast
    exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) _
  rw [hmod]
  ring

end GlobalTheory.CompanionTheory.PieDiag

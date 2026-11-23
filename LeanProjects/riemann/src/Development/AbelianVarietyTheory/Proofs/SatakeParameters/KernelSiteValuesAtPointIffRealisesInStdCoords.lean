import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalBasisCoordsAgainstBlockActionStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem realAt_iff_realises : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) (e : D.what₂.Tau → ℤ) (φ : (D.chTw u μ).cls j → (D.chTw u μ).Y j → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), (∀ y, φ (clsAt X H j La.1 La.2) y = (∏ τ, (D.chTw u μ).de j y τ ^ e τ)⁻¹ * frPoly (t.O u μ) j P y) → ∀ V, RealAt d j hj h La φ V ↔ Realises (sysS H X std) D (hT.gat_pos u w hg) j h (fun τ => e τ - cTw D j) (sPt d j hj La • P) (actC (sysS H X std) D (hT.gat_pos u w hg) j h (mM d j hj La) V)) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S d j hj h La e φ P hφ V
  have hp := J.pins.frm j hj
  have hde := (t.O u μ).frm_de j hj

  have hdetU : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, IsUnit ((A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ)).det := by
    intro A τ
    have e1 := RingHom.map_det (embT D τ) (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)
    rw [RingHom.mapMatrix_apply] at e1
    rw [← e1]
    exact (Matrix.isUnits_det_units A).map _
  have hmul : ∀ (A A' : GL (Fin (D.R.N j)) D.host.E) τ, ((A * A' : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) =
      (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * (A' : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) := by
    intro A A' τ
    rw [Units.val_mul, Matrix.map_mul]
  have hinv : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, ((A⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
      (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) = 1 := by
    intro A τ
    rw [← hmul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv' : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
      ((A⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) = 1 := by
    intro A τ
    rw [← hmul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMB : mM d j hj La * (bAt J j hj La.1)⁻¹ = J.A.crd j hj * (d.gam j hj La)⁻¹ := by
    unfold mM
    exact mul_inv_cancel_right _ _
  have hat : ∀ τ, (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) =
      (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
        ((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ) := by
    intro τ
    rw [hMB, ← hmul]
    rfl

  have alg : ∀ (z' : Fr D j hj) (f : Fr1 D (D.R.N j)),
      (∀ τ, f.1 τ = (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ) →
      d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j *
          dPow (bAt J j hj La.1).1 (fun _ => -(cTw D j)) * detF (cTw D j) z' *
          φ (clsAt X H j La.1 La.2) ((J.St j hj).eY.symm z') =
        (∏ τ, (f.1 τ).det ^ (-(e τ - cTw D j))) * GL3Theta.evFr D (sPt d j hj La • P) f.1 := by
    intro z' f hf
    have hfr : (t.O u μ).frm j ((J.St j hj).eY.symm z') = f.1 := by
      funext τ
      rw [hp, Equiv.apply_symm_apply, hf]
      rfl
    have hfp : frPoly (t.O u μ) j P ((J.St j hj).eY.symm z') = GL3Theta.evFr D P f.1 := by
      rw [← hfr]
      rfl
    have hdef : ∀ τ, (D.chTw u μ).de j ((J.St j hj).eY.symm z') τ = (f.1 τ).det := fun τ => by rw [hde, hfr]
    have hsm : GL3Theta.evFr D (sPt d j hj La • P) f.1 = sPt d j hj La * GL3Theta.evFr D P f.1 := by
      unfold GL3Theta.evFr
      rw [MvPolynomial.smul_eval]
    rw [hφ, hfp, hsm]
    simp only [hdef]
    have ha : ∀ τ, embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det ≠ 0 := fun τ =>
      ((Matrix.isUnits_det_units (J.A.crd j hj)).map (embT D τ)).ne_zero
    have hw : ∀ τ, (z'.1 τ).det ≠ 0 := fun τ => (z'.2 τ).ne_zero
    have hdf : ∀ τ, (f.1 τ).det = embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det * (z'.1 τ).det := by
      intro τ
      rw [hf, Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]
    have huB : dPow (uB J j hj La.1).1 (fun _ => -(cTw D j)) =
        ∏ τ, (embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det *
          embT D τ (bAt J j hj La.1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det) ^ (-(cTw D j)) := by
      unfold dPow uB
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Units.val_mul, Matrix.det_mul, map_mul]
    have hprod : dPow (bAt J j hj La.1).1 (fun _ => -(cTw D j)) * detF (cTw D j) z' * (∏ τ, (f.1 τ).det ^ e τ)⁻¹ =
        (∏ τ, (f.1 τ).det ^ (-(e τ - cTw D j))) * dPow (uB J j hj La.1).1 (fun _ => -(cTw D j)) := by
      rw [huB]
      unfold dPow detF
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hdf τ]
      have h1 := ha τ
      have h2 := hw τ
      rw [mul_zpow, mul_zpow, mul_zpow, neg_sub, zpow_sub₀ h1, zpow_sub₀ h2, zpow_neg, zpow_neg]
      field_simp
    unfold sPt
    linear_combination (d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j * GL3Theta.evFr D P f.1) * hprod
  unfold RealAt Realises
  constructor
  · intro hR f
    let z' : Fr D j hj := ⟨fun τ => ((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ) * f.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (f.2 τ)⟩
    let z : Fr D j hj := ⟨fun τ => (d.gam j hj La : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (z'.2 τ)⟩
    have hzz : IsTr (atInf (embT D) (d.gam j hj La).1) z' z := fun τ => rfl
    have hf' : ∀ τ, f.1 τ = (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ := by
      intro τ
      show _ = _ * (_ * _)
      rw [← Matrix.mul_assoc, hinv', Matrix.one_mul]
    have hfz : ∀ τ, f.1 τ = (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) * z.1 τ := by
      intro τ
      rw [hat]
      show _ = _ * _ * (_ * _)
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ)), hinv, Matrix.one_mul, hf']
    have key := (GlobalTheory.T.evalBasisCoords_against_blockAction (sysS H X std) D (hT.gat_pos u w hg) j h (gramC (gramN D j hj) (embT D)) (bAt J j hj La.1)
      (mM d j hj La) V z f hfz).1
    rw [← key, hR z z' hzz, alg z' f hf']
  · intro hR z z' hzz
    let f : Fr1 D (D.R.N j) := ⟨fun τ => (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (z'.2 τ)⟩
    have hfz : ∀ τ, f.1 τ = (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) * z.1 τ := by
      intro τ
      rw [hat, hzz τ]
      show _ = _ * _ * ((d.gam j hj La : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * _)
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ)), hinv, Matrix.one_mul]
    have key := (GlobalTheory.T.evalBasisCoords_against_blockAction (sysS H X std) D (hT.gat_pos u w hg) j h (gramC (gramN D j hj) (embT D)) (bAt J j hj La.1)
      (mM d j hj La) V z f hfz).1
    rw [key, hR f, alg z' f (fun τ => rfl)]

end GlobalTheory.TwV.DelA

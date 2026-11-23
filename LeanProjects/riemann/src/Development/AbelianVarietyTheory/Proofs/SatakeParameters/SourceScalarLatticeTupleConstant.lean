import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetRationalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatricesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeightsStatement
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem source_scalar_const : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j < D.R.m), Nonempty (Lv.comp (j + 1)) → ∀ La : (sysS H X std).Lt j, dPow (mM d j hj.le La).1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d j hj.le La * d.uS S j La = kS J j hj.le La.1) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S d j hj hne La
  have hW := GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j hj hne
  have hfr := (GlobalTheory.T.changedFrame_rational_unitary S d j hj.le (rkS _ _ hW.rk) La).2.2
  obtain ⟨e, he, hmu⟩ := GlobalTheory.T.stepCharacter_det_rationalIsometry S j hj
  have hgd := (GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S j hj.le).2 _ (d.mem j hj.le La)
  obtain ⟨q, hq⟩ := Formalism.L2.Ker.even_rankN D.R (j + 1)
  have hs : ∀ τ, (D.chTw u μ).sSharp j τ = e τ - ((D.R.N (j + 1) / 2 : ℕ) : ℤ) := by
    intro τ
    have h1 := (D.chTw u μ).sSharp_eq j hj τ
    rw [D.hcW_e u τ, ← he τ] at h1
    have h2 : D.R.N (j + 1) / 2 = q := by omega
    rw [h2]
    have h3 : ((D.R.N (j + 1) : ℕ) : ℚ) = (q : ℚ) + q := by exact_mod_cast hq
    unfold sExp' at h1
    rw [h3] at h1
    have h4 : ((D.chTw u μ).sSharp j τ : ℚ) = ((e τ - (q : ℤ) : ℤ) : ℚ) := by push_cast; rw [h1]; ring
    exact_mod_cast h4
  have hχ : d.chi j hj.le La ≠ 0 := by unfold Dec.chi; exact Units.ne_zero _
  have hcD : ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  unfold dPow sPt Dec.uS kS dPow
  rw [dif_pos hj.le, hmu j hj.le _ (d.mem j hj.le La), hgd.1]
  simp only []
  set n : ℤ := ((D.R.N (j + 1) / 2 : ℕ) : ℤ) with hn
  set c : ℤ := cTw D j with hc
  rw [show ∀ (A χ C B Mu P : ℂ), A * (χ * C ^ c * B) * (χ⁻¹ * Mu⁻¹ * P * C ^ (-c)) = A * B * Mu⁻¹ * P * (χ * χ⁻¹) * (C ^ c * C ^ (-c)) from
    fun _ _ _ _ _ _ => by ring]
  rw [mul_inv_cancel₀ hχ, ← zpow_add₀ hcD, add_neg_cancel, zpow_zero, mul_one, mul_one]
  rw [← Finset.prod_zpow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hm : (embT D τ) (mM d j hj.le La).1.det ≠ 0 := by rw [map_ne_zero]; exact (Matrix.isUnits_det_units _).ne_zero
  have hgn : (embT D τ) (d.gam j hj.le La).1.det ≠ 0 := by rw [map_ne_zero]; exact (Matrix.isUnits_det_units _).ne_zero
  have hb := congrArg (embT D τ) hfr
  rw [map_mul] at hb
  rw [← hb, hW.sh τ, hs τ]
  show (embT D τ) _ ^ _ * _ * ((embT D τ) _ ^ _)⁻¹ * ((embT D τ) (_ * _)) ^ _ = _
  rw [map_mul]
  generalize (embT D τ) (mM d j hj.le La).1.det = m at hm ⊢
  generalize (embT D τ) (d.gam j hj.le La).1.det = g at hgn ⊢
  generalize (embT D τ) (gMat J j hj.le 1).det = G
  generalize e τ = ee
  simp only [mul_zpow, zpow_neg, zpow_sub₀ hm, zpow_sub₀ hgn, zpow_add₀ hm, zpow_add₀ hgn]
  field_simp
  ring

end GlobalTheory.TwV.DelA

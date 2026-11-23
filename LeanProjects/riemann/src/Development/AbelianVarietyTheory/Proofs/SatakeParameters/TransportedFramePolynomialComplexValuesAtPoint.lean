import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelProjection
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteValuesAtPointIffRealisesInStdCoordsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvalBasisCoordsAgainstBlockAction
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetFrameMapEqComplexBlockActionScalarStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetStepScalarEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRows
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosTieAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteModelStageWeightsEqChainWeightsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem actC_actC_inv {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (i : ℕ) {n : ℕ}
    (h : (X.Pj i).m + 1 = n) (M : GL (Fin n) D.host.E) (V : XR (X.Pj i) ℂ) :
    actC X D pos i h M (actC X D pos i h M⁻¹ V) = V := by
  let z : Frames (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ)) := ⟨fun _ => 1, fun _ => by simp⟩
  let f : Fr1 D n := ⟨fun τ => (atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * z.1 τ, fun τ => by
    show IsUnit ((atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ : Matrix (Fin n) (Fin n) ℂ) * 1).det
    rw [mul_one]
    exact (Matrix.GeneralLinearGroup.det (atR D (M * (1 : GL (Fin n) D.host.E)⁻¹) τ)).isUnit⟩
  exact (evC_crdB_actC X D pos i h (fun _ => 1) 1 M V z f (fun _ => rfl)).2

theorem embT_det_ne_zero (D : D7) {n : ℕ} (M : GL (Fin n) D.host.E) (τ : D.what₂.Tau) : embT D τ M.1.det ≠ 0 := by
  have h0 : M.1.det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det M).ne_zero
    simpa using this
  exact (map_ne_zero _).2 h0

theorem transported_frame_realAt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La' : (sysS H X std).Lt (j + 1)) (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ), P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) (Formalism.L2.Ker.nuT D u j)) → (∀ y, φ (clsAt X H (j + 1) La'.1 La'.2) y = (∏ τ, (D.chTw u μ).de (j + 1) y τ ^ (D.chTw u μ).sDiv j τ)⁻¹ * frPoly (t.O u μ) (j + 1) P y) → ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, RealAt d (j + 1) hj h La' φ V ∧ MvPolynomial.map ι V = scT d S ι j La'.1 La'.2 • GlobalTheory.FrameB.tauV ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La' (phi0 (sysS H X std) D (hT.gat_pos u w hg) ι j P)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι
  intro d j hj h La' φ P hP hφ
  have hWt := GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j (by omega) ⟨La'.1⟩
  obtain ⟨-, -, -, hle, -⟩ := size_first_last_rows (sysS H X std) D (hT.gat_pos u w hg) j hWt.rk (nuT D u j) hWt.nu
  have hR : Realises (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P
      (phiC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P) := by
    obtain ⟨R0, hR0⟩ := GlobalTheory.T.frame_polynomials_weight_realised_next_level (sysS H X std) D (hT.gat_pos u w hg) j h _ hle P hP
    exact selOf_mem (relPhi (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h _) P ⟨(P, R0), hR0, rfl⟩
  refine ⟨sPt d (j + 1) hj La' • actC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (mM d (j + 1) hj La')⁻¹
    (phiC (sysS H X std) D (hT.gat_pos u w hg) (j + 1) h (wT (sysS H X std) D (hT.gat_pos u w hg) j) P), ?_, ?_⟩
  · rw [GlobalTheory.T.kernelSite_valuesAtPoint_iff_realisesInStdCoords S d (j + 1) hj h La' (fun τ => (D.chTw u μ).sDiv j τ) φ P hφ, map_smul, actC_actC_inv]
    have hw : (fun τ => (D.chTw u μ).sDiv j τ - cTw D (j + 1)) = wT (sysS H X std) D (hT.gat_pos u w hg) j :=
      funext fun τ => (hWt.dv τ).symm
    rw [hw]
    intro f
    have h1 := hR f
    simp only [GL3Theta.evFr, map_smul, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eval] at h1 ⊢
    rw [h1]
    ring
  · letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
    letI := algKfC S.E.toCEmb
    have hPT := (posTie_at S hPos ι hι).1
    have hFr := GlobalTheory.T.changedFrame_rational_unitary S d (j + 1) hj h La'
    have hτ := GlobalTheory.T.targetFrameMap_eq_complexBlockAction_scalar (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hPT d.fd2
      (ltC S.g S.hLT) (ltC_ne_zero _ _) j hWt.rk La' (mM d (j + 1) hj La') hFr.1 hFr.2.1 (nuT D u j) hWt.nu P hP
    have h45 := GlobalTheory.T.targetStep_scalar_eq S d j hj La'
    have hprod : dPow (mM d (j + 1) hj La').1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) *
        ∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ = 1 := by
      unfold dPow
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun τ _ => ?_
      rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (embT_det_ne_zero D _ τ))]
    have hc := ltC_ne_zero S.g S.hLT
    have key : ι (sPt d (j + 1) hj La') = scT d S ι j La'.1 La'.2 * (ltC S.g S.hLT ^ (∑ τ, szT (sysS H X std) D (hT.gat_pos u w hg) j τ) *
        ι (∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) := by
      rw [scT, dif_pos hj]
      have e1 : sPt d (j + 1) hj La' = d.uT S j (La'.1, La'.2) * kT J j hj La'.1 *
          ∏ τ, embT D τ (mM d (j + 1) hj La').1.det ^ wT (sysS H X std) D (hT.gat_pos u w hg) j τ := by
        rw [← h45, mul_comm (dPow _ _) (sPt _ _ _ _), mul_assoc, hprod, mul_one]
      rw [e1, map_mul, zpow_neg]
      field_simp
    rw [hτ, smul_smul, ← key, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

end GlobalTheory.TwV.DelA

end

import Mathlib
import GroundTheory.PAdicHodge.WAFracFrobAnn
import GroundTheory.PAdicHodge.WAFracAnnPt
import GroundTheory.PAdicHodge.WAFracOrbit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAFrac

open Laurent Filter Topology UniformSpace
open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris WAPeriodT

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔽" => frob ℂ_[p] p

theorem isDomain_bCrisPlus : IsDomain (BCrisPlus ℂ_[p] p) :=
  Function.Injective.isDomain (iotaPlus ℂ_[p] p) (iotaPlus_injective (K := ℂ_[p]))

abbrev radPhi : Set.Ioo (0 : ℝ) 1 := (𝔽).rootRadius (rhoMid p)

theorem inv_p_le_inRad_radPhi : (p : ℝ)⁻¹ ≤ ((inRad p (radPhi (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) := by
  have e : ((inRad p (radPhi (p := p)) : Set.Ioc (0 : ℝ) _) : ℝ) = rhoMid p :=
    congrArg Subtype.val ((𝔽).powRadius_rootRadius (rhoMid p))
  rw [e]; exact inv_p_lt_rhoMid.le

theorem phiPlus_injective : Function.Injective (phiPlus ℂ_[p] p) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have hσ := inv_p_le_inRad_radPhi (p := p)
  have h1 := annNorm_bcrisToAnn_pos hσ hx0 (annOut _ _)
  have h2 := annNorm_frobCirc (radPhi (p := p)) (bcrisToAnn hσ x)
  rw [frobCirc_bcrisToAnn _ hσ, hx, map_zero, (𝓣).annNorm_zero] at h2
  have := pow_pos h1 p
  linarith

section Points

variable {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0}

theorem annMap_ξAnn {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : Gal(PadicAlgCl p/K)) (P : (𝓣).Pt) :
    (galIso σ).annMap ((𝓣).ξAnn (ρ0 := ρ0) (σ0 := σ0) P.1) = (𝓣).ξAnn (galPt σ P).1 := by
  rw [TeichLift.ξAnn, TeichLift.TeichIso.annMap_coeAnn, TeichLift.ξAnn]
  congr 1
  apply Subtype.ext
  show (galIso σ).toB (algebraMap (WC p) (𝓣).B P.1) = algebraMap (WC p) (𝓣).B ((galIso σ).ψ P.1)
  rw [TeichLift.TeichIso.toB_algebraMap]

theorem annRes_ξAnn {ρ1 : Set.Ioo (0 : ℝ) 1} {σ1 : Set.Ioc (0 : ℝ) ρ1} (h : (ρ1 : ℝ) ≤ ρ0)
    (hs : (σ0 : ℝ) ≤ σ1) (ξ : (𝓣).int) :
    (𝓣).annRes h hs ((𝓣).ξAnn (ρ0 := ρ0) (σ0 := σ0) ξ) = (𝓣).ξAnn ξ := by
  rw [TeichLift.ξAnn, (𝓣).annRes_coeAnn]; rfl

theorem isUnit_of_eq_mul_of_ptRad_eq {P Q : (𝓣).Pt} {B : (𝓣).int} (h : P.1 = Q.1 * B)
    (hr : (𝓣).ptRad P.1 = (𝓣).ptRad Q.1) : IsUnit B := by
  rw [(𝓣).isUnit_int_iff]
  have h0 : (𝓣).red (P.1 : WC p) = (𝓣).red (Q.1 : WC p) * (𝓣).red (B : WC p) := by
    rw [h, Subring.coe_mul, map_mul]
  have hP : ‖(𝓣).red (P.1 : WC p)‖ = (𝓣).ptRad P.1 := by rw [← coeff_zero]; rfl
  have hQ : ‖(𝓣).red (Q.1 : WC p)‖ = (𝓣).ptRad Q.1 := by rw [← coeff_zero]; rfl
  have hQ0 : 0 < (𝓣).ptRad Q.1 := (𝓣).ptRad_pos' Q.2
  have := congrArg norm h0
  rw [norm_mul, hP, hQ, hr] at this
  have h1 : (𝓣).ptRad Q.1 * 1 = (𝓣).ptRad Q.1 * ‖(𝓣).red (B : WC p)‖ := by rw [mul_one]; exact this
  exact (mul_left_cancel₀ hQ0.ne' h1).symm

theorem annEval_ξAnn_ne_zero {P Q : (𝓣).Pt} (hQ : (𝓣).ptRad Q.1 ∈ Set.Icc (σ0 : ℝ) ρ0)
    (hr : (𝓣).ptRad P.1 = (𝓣).ptRad Q.1) (hPQ : ¬ ∃ u : (𝓣).int, IsUnit u ∧ P.1 = u * Q.1) :
    (𝓣).annEval Q.2 hQ ((𝓣).ξAnn (ρ0 := ρ0) (σ0 := σ0) P.1) ≠ 0 := by
  intro h0
  rw [ξAnn_eq_toAnn, annEval_toAnn, (𝓣).ptEval_ξExt_eq Q hQ.2, (𝓣).toUntiltField_eq_zero_iff] at h0
  obtain ⟨B, hB, hPB⟩ := ((𝓣).toUntilt_eq_zero_iff (ξ := Q.1)).1 h0
  have hPB' : P.1 = Q.1 * ⟨B, hB⟩ := Subtype.ext hPB
  exact hPQ ⟨⟨B, hB⟩, isUnit_of_eq_mul_of_ptRad_eq hPB' hr, by rw [hPB', mul_comm]⟩

end Points

end WAFrac

end GroundTheory.PAdicHodge

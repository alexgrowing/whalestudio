import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LineScalingNorm.ConstantOneMemNonvanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

noncomputable section

theorem line_move_formula : LineMove := by
  intro Wp Wq _ _ _ _ _ _ P Bs μ' hμ' _hpl ζ _hζ h hh h' hh' he Pr hPr σ Y hY
  obtain ⟨hYF, hYP⟩ := hY
  have hhi := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh
  have hh'i := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh'
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨hp1, hp2, hpe⟩ := hp
    have hq1 : h⁻¹ * p.1 * h ∈ UWset P.k P.r Bs.z :=
      Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul (Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hhi hp1) hh
    have hq2 : h' * p.2 * h'⁻¹ ∈ UWset P.k P.r Bs.z' :=
      Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul (Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hh' hp2) hh'i
    have hback : NF.muZ P.k P.r μ' ζ = h⁻¹ * NF.muZ P.k P.r Bs.μsec ζ * h'⁻¹ := by
      rw [he, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Matrix.one_mul,
        Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh', Matrix.mul_one]
    have hq : ((h⁻¹ * p.1 * h, h' * p.2 * h'⁻¹) : Q.Mx P.k P.r × Q.Mx P.k P.r) ∈
        NF.Stab P.k P.r Bs.z Bs.z' μ' ζ := by
      refine ⟨hq1, hq2, ?_⟩
      change h⁻¹ * p.1 * h * NF.muZ P.k P.r μ' ζ * (h' * p.2 * h'⁻¹) = NF.muZ P.k P.r μ' ζ
      have e : h⁻¹ * p.1 * h * NF.muZ P.k P.r μ' ζ * (h' * p.2 * h'⁻¹) =
          h⁻¹ * (p.1 * (h * NF.muZ P.k P.r μ' ζ * h') * p.2) * h'⁻¹ := by
        simp only [Matrix.mul_assoc]
      rw [e, ← he, hpe, ← hback]
    have key : (Bs.π (h⁻¹ * p.1 * h)).comp (Y.comp (Bs.π' (h' * p.2 * h'⁻¹))) = Y := hYF _ hq
    have e1 : (Bs.π p.1).comp (Bs.π h) = (Bs.π h).comp (Bs.π (h⁻¹ * p.1 * h)) := by
      rw [← Bs.π_rep.2 _ hp1 _ hh, ← Bs.π_rep.2 _ hh _ hq1]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hh, Matrix.one_mul]
    have e2 : (Bs.π' h').comp (Bs.π' p.2) = (Bs.π' (h' * p.2 * h'⁻¹)).comp (Bs.π' h') := by
      rw [← Bs.π'_rep.2 _ hh' _ hp2, ← Bs.π'_rep.2 _ hq2 _ hh']
      congr 1
      rw [Matrix.mul_assoc, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh', Matrix.mul_one]
    change (Bs.π p.1).comp (((Bs.π h).comp (Y.comp (Bs.π' h'))).comp (Bs.π' p.2)) = (Bs.π h).comp (Y.comp (Bs.π' h'))
    calc (Bs.π p.1).comp (((Bs.π h).comp (Y.comp (Bs.π' h'))).comp (Bs.π' p.2))
        = ((Bs.π p.1).comp (Bs.π h)).comp (Y.comp ((Bs.π' h').comp (Bs.π' p.2))) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = ((Bs.π h).comp (Bs.π (h⁻¹ * p.1 * h))).comp (Y.comp ((Bs.π' (h' * p.2 * h'⁻¹)).comp (Bs.π' h'))) := by
          rw [e1, e2]
      _ = (Bs.π h).comp (((Bs.π (h⁻¹ * p.1 * h)).comp (Y.comp (Bs.π' (h' * p.2 * h'⁻¹)))).comp (Bs.π' h')) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = (Bs.π h).comp (Y.comp (Bs.π' h')) := by rw [key]
  · set a := SSn.nu0 P.k P.r Bs.z Bs.z' μ' ζ with ha
    have hYP' : (Pr σ a).comp Y = Y := hYP
    have hν : SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ = h *ᵥ a := by
      rw [ha]
      unfold SSn.nu0 SSn.unitH
      rw [he, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh'.2.2,
        Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.TF.prWv_uw Bs.z_mem Bs.T_pos hh, Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1,
        Matrix.mulVec_smul]
    have e0 : (Bs.π h⁻¹).comp (Bs.π h) = 1 := by
      rw [← Bs.π_rep.2 _ hhi _ hh, Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hh, Bs.π_rep.1]
    have e0' : ∀ T : Wq →L[ℂ] Wp, (Bs.π h⁻¹).comp ((Bs.π h).comp T) = T := by
      intro T
      ext v
      have k1 := DFunLike.congr_fun e0 (T v)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at k1 ⊢
      exact k1
    change (Pr σ (SSn.nu0 P.k P.r Bs.z Bs.z' Bs.μsec ζ)).comp ((Bs.π h).comp (Y.comp (Bs.π' h'))) =
      (Bs.π h).comp (Y.comp (Bs.π' h'))
    rw [hν, hPr.2.1 h hh σ a]
    calc ((Bs.π h).comp ((Pr σ a).comp (Bs.π h⁻¹))).comp ((Bs.π h).comp (Y.comp (Bs.π' h')))
        = (Bs.π h).comp ((Pr σ a).comp ((Bs.π h⁻¹).comp ((Bs.π h).comp (Y.comp (Bs.π' h'))))) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = (Bs.π h).comp (((Pr σ a).comp Y).comp (Bs.π' h')) := by
          rw [e0' (Y.comp (Bs.π' h'))]; simp only [ContinuousLinearMap.comp_assoc]
      _ = (Bs.π h).comp (Y.comp (Bs.π' h')) := by rw [hYP']

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.SR

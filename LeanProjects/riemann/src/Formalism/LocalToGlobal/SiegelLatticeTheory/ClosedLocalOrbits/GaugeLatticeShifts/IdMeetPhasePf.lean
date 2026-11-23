import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKey
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut

noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full

theorem idMeetPhaseC_of (hK : IdMeetKeyC) : IdMeetPhaseC := by
  intro D X Y u hneat _ ρ t hid hmeet
  obtain ⟨-, hlin⟩ := hK D X Y u hneat ρ ρ t hid hmeet
  have hR : RatLink X t.pt t.lin := t.rep.2.1
  have hN : t.pt.1 ∈ X.NinfU u := Formalism.L2.SG.Pf.nLamNinf_holds D X u _ t.pt t.lin hR hlin
  have hNf : t.pt.2 ∈ X.NfinU u := Formalism.L2.SG.Pf.nLamNfin_holds D X u _ t.pt t.lin hR hlin
  obtain ⟨h1, hmul, hinv⟩ := Formalism.L2.SG.Pf.psiInfChar_holds D X u
  obtain ⟨-, hchi, -⟩ := Formalism.L2.SG.Pf.nilradical_conj_level' D X Y u ρ t.pt t.lin hlin hR
  have hprod := Formalism.L2.SG.Pf.psiProd_all D X u t.pt (ratLink_mem X hR) hN hNf
  refine ⟨hinv _ hN, ?_⟩
  have hψ1 : X.psiInfU u 1 = 1 := by
    have h11 := (hmul 1 h1 1 h1).2
    rw [mul_one] at h11
    have hn := Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u 1
    have h0 : X.psiInfU u 1 ≠ 0 := by
      intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    exact mul_left_cancel₀ h0 (h11.symm.trans (mul_one _).symm)
  have hinvψ : X.psiInfU u t.pt.1⁻¹ * X.psiInfU u t.pt.1 = 1 := by
    rw [← (hmul _ (hinv _ hN) _ hN).2, inv_mul_cancel, hψ1]
  have hconj : starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = X.psiInfU u t.pt.1 := by
    have hn := Formalism.L2.SG.RealObj.InfCut.norm_psiInfU X u t.pt.1⁻¹
    have hz : starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = (X.psiInfU u t.pt.1⁻¹)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]; simp
    rw [hz, inv_eq_of_mul_eq_one_right hinvψ]
  show X.chi2 ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * t.pt.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *
    starRingEnd ℂ (X.psiInfU u t.pt.1⁻¹) = 1
  rw [hchi, hconj, mul_comm]
  exact hprod

end Formalism.L2.SG.Pf.IdMeet

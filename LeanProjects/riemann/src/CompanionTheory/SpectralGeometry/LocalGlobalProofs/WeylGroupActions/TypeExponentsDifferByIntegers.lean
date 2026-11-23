import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
import Formalism.HermitianCurvature.FrameExists2
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.CapelliParamsDiffInt

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.GapInt

theorem type_param_diff_int : ∀ (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : B.Mat k r → (Wq →L[ℂ] Wq)) (u : ℕ → ℝ), inWb k r z → 0 < Tz k r z → IsType k r z π u → ∀ i ∈ Finset.Icc 1 k, ∀ j ∈ Finset.Icc 1 k, ∃ N : ℤ, u i - u j = (N : ℝ) := by
  intro Wq _ _ _ k r z π u hz hT hty i hi j hj
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Bs, hB⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists hz hT
  obtain ⟨hnt, hrep, hcont, -, -, hcap⟩ := hty
  have hR : Qr.IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨hgl, hq⟩ := Formalism.FourierDecayAlt.P.frame_general_linear Wq (n + 1) r (n + 1) z π Bs hR hB
  have hc : ∀ w v, qdet (Qr.EB π Bs) w v =
      Qr.cpol (fun a : Fin (n + 1) => (u ((a : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2) w • v := by
    intro w v
    rw [← hq w v, hcap Bs hB w v, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
    congr 1
    unfold Qr.cpol
    refine Finset.prod_congr rfl (fun a _ => ?_)
    ring
  obtain ⟨N, hN⟩ := GlobalTheory.CompanionTheory.GapLie.capelli_params_diff_int Wq (n + 1) (Qr.EB π Bs) _ hgl hc
    ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩
  refine ⟨N, ?_⟩
  have e1 : i - 1 + 1 = i := by omega
  have e2 : j - 1 + 1 = j := by omega
  simp only [e1, e2] at hN
  have h : ((u i : ℝ) : ℂ) - (u j : ℂ) = (N : ℂ) := by linear_combination hN
  exact_mod_cast h

end GlobalTheory.CompanionTheory.GapInt

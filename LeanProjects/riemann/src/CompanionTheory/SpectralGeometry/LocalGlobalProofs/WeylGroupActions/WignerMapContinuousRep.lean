import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.OmgNMulN
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.OmgLeftRight

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmgWigEquiv

theorem wigEquiv_omg (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Wq' : Type)
    [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (π' : B.Mat k r → (Wq →L[ℂ] Wq)) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (d : ℕ)
    (A : (Fin (2 * r + k + 1) → ℂ) → (Wq' →L[ℂ] Wq))
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    (hA : GlobalTheory.WigSh.WigMap k r z' π'' π' d A) (hπ : IsCRepOn (UWset k r z') π'') :
    WigEquiv z z' π' π'' (fun g => A (GlobalTheory.WigSh.omg k r z z' (g))) := by
  refine ⟨fun g hg _ n hn n' hn' => ?_, fun g hg _ h hh => ?_, fun g hg _ h hh => ?_⟩
  · exact congrArg A (GlobalTheory.CompanionTheory.OmegaBiInv.omg_N_mul_N k r z z' hz hz' g hg n hn n' hn')
  · exact congrArg A ((GlobalTheory.CompanionTheory.OmgUW.omg_left_right k r z z' hz hT hz' hT' g hg).1 h hh)
  · have hi := Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh
    have h1 := (GlobalTheory.CompanionTheory.OmgUW.omg_left_right k r z z' hz hT hz' hT' g hg).2 h hh
    have h2 := hA.2.1 h⁻¹ hi (GlobalTheory.WigSh.omg k r z z' g)
    have h3 : (π'' h⁻¹).comp (π'' h) = ContinuousLinearMap.id ℂ Wq' := by
      rw [← hπ.2 _ hi _ hh, Formalism.FourierDecayAlt.P.LeftDerivativeCurves.uh_inv_mul hh.1, hπ.1]
      rfl
    show A (GlobalTheory.WigSh.omg k r z z' (g * h)) = (π' h⁻¹).comp ((A (GlobalTheory.WigSh.omg k r z z' g)).comp (π'' h))
    rw [h1, ← ContinuousLinearMap.comp_assoc, ← h2, ContinuousLinearMap.comp_assoc, h3,
      ContinuousLinearMap.comp_id]

end GlobalTheory.CompanionTheory.OmgWigEquiv

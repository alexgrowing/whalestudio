import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.TypeGlModule

theorem hyp_and_adj :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ)
      (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ)
      (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)),
      inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L →
      (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) →
      IsFrameOf (n + 1) r [z] B →
      Hyp (EB π B) β L ∧ ∀ a b x y, inner ℂ (EB π B a b x) y = inner ℂ x (EB π B b a y) := by
  intro V _ _ _ n r z π u β L B hz hT hty hL hu hB
  obtain ⟨hnt, hrep, hcont, hunit, hirr, hcap⟩ := hty
  have hR : IsRepW (n + 1) r z π := ⟨hrep, hcont⟩
  obtain ⟨hgl, hq⟩ := Formalism.FourierDecayAlt.P.frame_general_linear V (n + 1) r (n + 1) z π B hR hB
  refine ⟨?_, fun a b x y => Formalism.FourierDecayAlt.P5.Kfp.EB_adj hrep hcont hunit hB a b x y⟩
  refine ⟨hgl, ⟨hnt, fun S hS =>
    hirr S (Formalism.FourierDecayAlt.P.lie_stabilizer V (n + 1) r z π B hz hT hR hB S hS)⟩, hL, ?_⟩
  intro w v
  rw [← hq w v, hcap B hB w v, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
  congr 1
  unfold cpol shf
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [← hu j]
  ring

end GlobalTheory.TypeGlModule

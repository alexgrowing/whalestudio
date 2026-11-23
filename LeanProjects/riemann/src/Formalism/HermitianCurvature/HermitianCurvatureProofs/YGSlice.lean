import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizePtG

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def YGSlice : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h' : C.LPt) (m ρ : ℕ)
    (e1 : r = D.ptSize h' + (m + 2) + ρ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Φ : G.Mat (m + 2) → V) (L : V →L[ℂ] E) (γ : B.Mat k ρ) (Kc : Set ℂ) (K a : ℝ),
    D.IsLocPt h' (D.ptSize h') → (0 : ℂ) ∉ Kc → ((m : ℝ) + 1) * ((m : ℝ) + 4) < a →
    (∀ Z : G.Mat (m + 2), G.detM Z ≠ 0 → ContinuousAt Φ Z ∧ ‖Φ Z‖ ≤ K * (1 + ‖Z‖) ^ (-a)) →
    (∀ Z : G.Mat (m + 2), G.detM Z ≠ 0 → G.detM Z ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc →
      L (Φ Z) = U.PhiFun k ρ (D.ptPerm h') (D.ptDiag h') (D.castV e1 z) (D.castV e1 z')
        (D.castF e1.symm F) Z γ) →
    ∀ q, okG m Kc q →
    Integrable (fun ξ : U.Xi k (D.ptSize (ptG h' m q)) 0 (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) =>
        U.psiStar k (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.castV (by rw [ptSize_ptG]; omega) z)
          (D.castV (by rw [ptSize_ptG]; omega) z') ξ •
          D.castF (by rw [ptSize_ptG]; omega) F
            (U.gaXi k (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.ptDiag (ptG h' m q)) ξ
              (fun a => a.elim0) (D.castM (by rw [ptSize_ptG]; omega) γ)))
      (U.muXi k (D.ptSize (ptG h' m q)) 0 (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q))) →
    L (yG U.betaU m Φ q) = D.sliceAt k r z z' F (ptG h' m q) (D.castM (by rw [ptSize_ptG]; omega) γ)

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

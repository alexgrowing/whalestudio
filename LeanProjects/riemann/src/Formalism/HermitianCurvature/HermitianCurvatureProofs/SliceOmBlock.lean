import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def kapB (n : ℕ) : ℝ := Real.pi ^ ((n + 1) * (n + 4) / 2)

theorem ptSize_two (h : C.LPt) (n : ℕ) (t c : ℂ) :
    D.ptSize (h ++ [(n + 1, t), (1, c)]) = D.ptSize h + (n + 1 + 1) := by
  simp [D.ptSize, List.map_append, List.sum_append]

def SliceOmBlock : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h p : C.LPt) (n : ℕ) (t c : ℂ)
    (hp : p = h ++ [(n + 1, t), (1, c)]) (hle : D.ptSize p ≤ r) (γ : B.Mat k (r - D.ptSize p)),
    D.IsLocPt p (D.ptSize p) →
    Integrable (fun ξ : U.Xi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar k (r - D.ptSize p) (D.ptPerm p) (D.castV (by omega) z) (D.castV (by omega) z') ξ •
          D.castF (by omega) F (U.gaXi k (r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p)) →
    D.sliceAt k r z z' F p γ =
      ((kapB n : ℝ) : ℂ) •
        G.OmBlock U.betaU (n + 1) (fun Z => U.PhiFun k (r - D.ptSize p) (D.ptPerm h) (D.ptDiag h)
          (D.castV (by subst hp; rw [ptSize_two] at hle ⊢; omega) z)
          (D.castV (by subst hp; rw [ptSize_two] at hle ⊢; omega) z')
          (D.castF (by subst hp; rw [ptSize_two] at hle ⊢; omega) F) Z γ) t c

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

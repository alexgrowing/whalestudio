import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def SliceIntCut : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (w : List C.Letter) (f : B.Mat P0.k P0.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ)
    (ε : ℝ) (i : ℕ) (hi : i ≤ P0.r),
    1 ≤ i → 2 ≤ P0.k → B.CkOn ⊤ (B.GV P0.k P0.r) f → (∃ R : ℝ, ∀ g ∈ B.GV P0.k P0.r, f g ≠ 0 → B.gN g ≤ R) →
    C6.IsCut0 χ → 0 < ε → ∀ (p : C.LPt) (hp : D.IsLocPt p i), ∀ (e : Wd.Ix (Fin w.length)),
    ∀ γ ∈ B.GV P0.k (P0.r - D.ptSize p),
    Integrable (fun ξ : U.Xi P0.k (D.ptSize p) 0 (P0.r - D.ptSize p) (D.ptPerm p) =>
        U.psiStar P0.k (P0.r - D.ptSize p) (D.ptPerm p) (D.castV (by have := hp.2; omega) T.base.z) (D.castV (by have := hp.2; omega) T.base.z') ξ •
          D.castF (by have := hp.2; omega) (D.uwG P0.k P0.r T.base.z T.base.z' (D.cutF T.base χ f ε) i hi w e)
            (U.gaXi P0.k (P0.r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
      (U.muXi P0.k (D.ptSize p) 0 (P0.r - D.ptSize p) (D.ptPerm p))

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

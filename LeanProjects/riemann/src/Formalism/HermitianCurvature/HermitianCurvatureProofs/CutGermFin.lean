import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermMean
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermContinuityAllLevels

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

theorem germCutPD_of_data (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hχ : C6.IsCut0 χ)
    (hnn : ∀ y, 0 < nn y) (hL : GermDataLowAll) (hT : GermDataTopAll) : GermCutPD p nn χ F Y K N :=
  germCutPD_of_parts hA p nn χ F Y K N Cb hCb hF hχ hnn germ_continuity_all_levels hL hT germ_mean_property

theorem block_growth_bound_of_compact_coef_of_germ_data (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hG : KB.CptCoef p.T.base G) (hnn : ∀ y, 0 < nn y)
    (hL : GermDataLowAll) (hT : GermDataTopAll) : TBB.BlockGrowthBound p nn G Y K N :=
  block_growth_bound_of_germ_data hA p nn G Y K N Cb hCb hG hnn germ_continuity_all_levels hL hT germ_mean_property

end Formalism.FourierDecayAlt.P.CutBP

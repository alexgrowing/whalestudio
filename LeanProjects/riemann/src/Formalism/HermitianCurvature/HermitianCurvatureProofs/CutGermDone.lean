import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermFin
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermLowAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopAll

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt

theorem germ_truncation_positive (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F) (hχ : C6.IsCut0 χ)
    (hnn : ∀ y, 0 < nn y) : GermCutPD p nn χ F Y K N :=
  germCutPD_of_data hA p nn χ F Y K N Cb hCb hF hχ hnn germ_data_low_levels germ_data_top_level

theorem block_growth_bound_of_compact_coef (hA : P5.ThmPActual) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ)
    (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hG : KB.CptCoef p.T.base G) (hnn : ∀ y, 0 < nn y) :
    TBB.BlockGrowthBound p nn G Y K N :=
  block_growth_bound_of_compact_coef_of_germ_data hA p nn G Y K N Cb hCb hG hnn germ_data_low_levels germ_data_top_level

end Formalism.FourierDecayAlt.P.CutBP

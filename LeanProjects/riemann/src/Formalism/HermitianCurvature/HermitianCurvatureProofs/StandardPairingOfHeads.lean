import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def PStdOfHeads : Prop := KB.RadHead → KB.HeadTop → KB.PStd

theorem pStdOfHeads : PStdOfHeads := fun hRH hHT =>
  pStdOfParts hRH hHT Formalism.FourierDecayAlt.P.module_form_eq_radial_form_one Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar

theorem pStdCpt_of_heads (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) :=
  pStd_cpt_of_parts hP hRH hHT Formalism.FourierDecayAlt.P.module_form_eq_radial_form_one Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar

end Formalism.FourierDecayAlt.P.PBO

theorem Formalism.FourierDecayAlt.P.standard_pairing_of_heads : Formalism.FourierDecayAlt.P.PBO.PStdOfHeads := Formalism.FourierDecayAlt.P.PBO.pStdOfHeads

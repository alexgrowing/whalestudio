import Formalism.HermitianCurvature.HermitianCurvatureProofs.WordCorrespondence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousHsInner

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.FourierDecayAlt

def PStdOfParts : Prop := KB.RadHead → KB.HeadTop → FormOne → ZetaNormExists → KB.PStd

theorem pStdOfParts : PStdOfParts := fun hRH hHT hOne hZN hP =>
  pStd_of hRH hHT hOne hZN
    (fun Wp Wq _ _ _ _ _ _ P p F w h h' hh hh' Cb hθ hF hw => by
      have hPc : P5.ThmPActualCpt := by
        intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
        obtain ⟨K, h1, h2, h3, h4⟩ := hP Wp Wq S P z z' π π' X μ L st l0 D A mm hD hl1 hl2 hz hz' hπ hπ' hA hmm
        exact ⟨K, h1, h2, h3, fun F ε hε hF _ hG => h4 F ε hε hF hG⟩
      exact topContOn_of hPc hHT Wp Wq P p F w h h' hh hh' Cb hθ hF hw) hP

theorem pStd_cpt_of_parts (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) (hOne : FormOne)
    (hZN : ZetaNormExists) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) :=
  pStd_of_cpt hP hRH hHT hOne hZN (topContOn_of hP hHT)

end Formalism.FourierDecayAlt.P.PBO

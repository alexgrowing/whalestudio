import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HeightAddLogNonneg
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition

set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.HtTopG
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz} {i : Fin D.R.m} {Y : Cov p i}
end Point
theorem height_of_meanAll_bound : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovHt.ShortAlt → _root_.GlobalTheory.CovHt.GeometricCondition → _root_.GlobalTheory.CovHt.MultiplicityConstantCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → D.R.m ^ 2 ≤ D.R.k → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Y.d.l₂.M'.primeFactors.card ≤ 15 → MeanAll Y.U (xiR D) (ell D) C) →
    _root_.GlobalTheory.CovTop.HeightCondition := by
  intro hPX hP hDG hSz hDg hSh hGe hMu hBu hDS
  obtain ⟨C0, h0, hDS⟩ := hDS
  refine Closed.imp ((((((hDG.and hSz).and hDg).and hSh).and hGe).and hMu).and hBu) ?_
  intro eps Fm CH _ hF
  obtain ⟨⟨⟨⟨⟨⟨⟨C1, -, a1⟩, ⟨C2, -, a2⟩⟩, ⟨C3, -, a3⟩⟩, ⟨C4, c4, a4⟩⟩, ⟨C5, -, a5⟩⟩, ⟨C6, c6, a6⟩⟩, ⟨C7, c7, a7⟩⟩ := hF
  refine ⟨C4 + C6 + C7 + C0 * C7, by positivity, ?_⟩
  obtain ⟨x0, hall⟩ := ((((((a1.and a2).and a3).and a4).and a5).and a6).and a7)
  refine ⟨x0, fun x hx hle ι p hp i hm Y hY u1 hq => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hall x hx hle ι p hp
  have hDGa := b1 i hm Y hY
  obtain ⟨hb1, hbE, -, -, -, -, hρ⟩ := b2 i
  have hU : 0 ≤ unitE p := by linarith
  have hρ1 : rhoB (dat p i) u1 < 1 := ((hρ hm).2 u1 hq).2.2.1
  have hBu := b7 i hm Y hY u1 hq
  exact _root_.GlobalTheory.CovHt.HtTopG.heightAt_eq_of_cover hPX hP hY.1 (_root_.GlobalTheory.CovHt.cover_height_comparison hP _ _ _ _ _ _) h0 c4 c6 c7 hU
    (hDS _ p.T p.fw.laws (Formalism.BasicNotions.ParameterChoice'.m_sq_le_k (Fm.params x hx ι)) ((i : ℕ) + 1) (by omega) hm Y _ _ hY.1 hBu.1) hDGa.2.2.2.2.2.2.1 hρ1
    (b3 i hm Y hY u1 hq) (b4 i hm Y hY u1 hq) (b5 i hm Y hY u1 hq) (b6 i hm Y hY u1 hq) hBu
end GlobalTheory.CovHt.HtTopG
end
end
end

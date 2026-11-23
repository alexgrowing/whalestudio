import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.UnramifiedPointsOfCMDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsDeepLevelStatement

section
set_option autoImplicit false
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
namespace GlobalTheory.UnramCover
theorem unramified_points_at_deep_level : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T →
    InR D j → Y.Good e o → UnramPts Y.d.Xo₂ Y.d.c₂ (badPrimes T.Q.H Y.d.l₂) := by
  intro hP D T j Y e o hL hj hY
  have hLaws := GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover D T j Y e o hL hj hY
  obtain ⟨-, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hL.pins j hj
  have h6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  exact _root_.GlobalTheory.T.cm_points_unramified hP _ T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ (by omega)
    (Or.inr (Or.inr ⟨by omega, hLaws.line⟩)) hLaws.good
end GlobalTheory.UnramCover
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_points_of_deep_cover : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → UnramPts Y.d.Xo₂ Y.d.c₂ (badPrimes T.Q.H Y.d.l₂) := by
  first | exact @_root_.GlobalTheory.UnramCover.unramified_points_at_deep_level | exact _root_.GlobalTheory.UnramCover.unramified_points_at_deep_level | (intros; apply _root_.GlobalTheory.UnramCover.unramified_points_at_deep_level <;> assumption)
end

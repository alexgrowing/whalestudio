import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPointsGoodLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCoverStatement

set_option autoImplicit false

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.UnramCover

theorem unramPts_deep : Hypotheses2 → ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T →
    InR D j → Y.Good e o → UnramPts Y.d.Xo₂ Y.d.c₂ (badPrimes T.Q.H Y.d.l₂) := by
  intro hP D T j Y e o hL hj hY
  have hLaws := GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover D T j Y e o hL hj hY
  obtain ⟨-, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D T.Q hL.pins j hj
  have h6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  exact GlobalTheory.T.unramified_points_good_level hP _ T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ (by omega)
    (Or.inr (Or.inr ⟨by omega, hLaws.line⟩)) hLaws.good

end GlobalTheory.UnramCover

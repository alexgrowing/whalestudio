import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValueStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRouteSubmoduleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowEx

theorem constEx_of : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → ConstEx := by
  intro hw hm h1 h2 h3 h4 h5
  obtain ⟨C1, H1⟩ := GlobalTheory.T.matched_theta_integral_value h1 h2 h3 h4 h5
  obtain ⟨C2, H2⟩ := GlobalTheory.T.polynomial_route_submodule hw h1 h2 hm h3 h4 h5
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, K1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x2, K2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  have k1 := K1 D large₂ he (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS
  have k2 := K2 D large₂ he (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS
  intro G W hW B
  obtain ⟨rm, hrm⟩ := GlobalTheory.RowTest.exists_match_over hS.core.lev hS.core.chain hW
  choose r hr1 hr2 hr3 hr4 using k2 G W hW B rm hrm
  let rel' : ∀ i j : ℕ, Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) := fun i j =>
    if h : i < D.R.m ∧ j < D.R.m then r ⟨i, h.1⟩ ⟨j, h.2⟩ else rm.rel i j
  have e : ∀ i j : Fin D.R.m, rel' i j = r i j := fun i j => dif_pos ⟨i.2, j.2⟩
  let ρ : RealMatch W := { rm with
    rel := rel'
    onto_big := fun i j a => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr1 ⟨i, h.1⟩ ⟨j, h.2⟩ a
      · simp only [rel', dif_neg h]; exact rm.onto_big i j a
    onto_small := fun i j b => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr2 ⟨i, h.1⟩ ⟨j, h.2⟩ b
      · simp only [rel', dif_neg h]; exact rm.onto_small i j b
    proper := fun i j => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr3 ⟨i, h.1⟩ ⟨j, h.2⟩
      · simp only [rel', dif_neg h]; exact rm.proper i j }
  have hρ : ρ.Over R := hrm
  have hc : ∀ i j t, ∃ c, IsSquareConst W B ρ t i j c := by
    intro i j t
    obtain ⟨c, hc⟩ := hr4 i j ρ rfl rfl (e i j) t
    refine ⟨c, fun M hM Θ Θ' hΘ z g g₁ hz => ?_⟩
    obtain ⟨J, hJ⟩ := k1 G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁
    obtain ⟨z₀, hz₀, hconv₀, hid⟩ := hc M hM Θ Θ' hΘ g g₁
    rw [hJ z₀ hconv₀.2] at hid
    have hI : ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * J := by
      apply mul_left_cancel₀ hz₀; rw [hid]; ring
    rw [hJ z hz.2, hI]; ring
  choose c hc using hc
  exact ⟨ρ, fun i j t => c i j t, hρ, fun i j t => hc i j t⟩

end GlobalTheory.RowEx

end

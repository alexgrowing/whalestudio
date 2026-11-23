import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiGridVertexRankAddLtTwoExponentAddCentre

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SquareInfGap

theorem square_infExp_gap : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ a b : D.what₂.Tau → ℚ, ∀ (t : T) (τ : D.what₂.Tau), HasInfExp D (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) τ (a τ) ∧ HasInfExp D (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) τ (b τ) ∧ 2 * (a τ - b τ) < -((rankV D (i + 1) (j + 1) + rankV D i j : ℕ) : ℚ) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro _ i j
  have hε : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = rankV D i j % 2 := by
    show (G.V (.grid (i : ℕ) (j : ℕ))).rank % 2 = _
    rw [(node_isV G hL (X := .grid (i : ℕ) (j : ℕ)) ⟨i.2.le, j.2.le⟩).rank]
    rfl
  refine ⟨fun τ => -(D.hc τ).e ⟨j, j.2⟩ + ((rankV D i j % 2 : ℕ) : ℚ) * (1 / 2),
    fun τ => (cen D 1 τ (D.R.m - i) : ℚ) + ((rankV D i j % 2 : ℕ) : ℚ) * (1 / 2), fun t τ => ⟨?_, ?_, ?_⟩⟩
  · have h := GlobalTheory.SquareExps.alpha_exp (G := G) hL t i j j.2 τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha, hε] at h
    exact h
  · have h := GlobalTheory.SquareExps.beta_exp (G := G) hL i j i.2 τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps] at h
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps, hε] at h
    exact h
  · have key := GlobalTheory.ChiGrid.rankV_add_lt_two_e_add_two_cen (D := D) 1 τ i j i.2 j.2
    push_cast at key ⊢
    linarith

end GlobalTheory.SquareInfGap

end

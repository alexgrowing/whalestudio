import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.CompHS.WeightGapAntitone

theorem antitone_of_gap_nonneg {N : ℕ} (v : Fin N → ℤ) (h : ∀ k, k + 1 < N → 0 ≤ gap v k) : Antitone v := by
  cases N with
  | zero => exact fun a => a.elim0
  | succ n =>
    refine Fin.antitone_iff_succ_le.2 fun i => ?_
    have := h i (by omega)
    rw [gap, dif_pos (by omega)] at this
    have e1 : (⟨(i : ℕ), by omega⟩ : Fin (n + 1)) = Fin.castSucc i := rfl
    have e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (n + 1)) = i.succ := rfl
    rw [e1, e2] at this
    omega

end GlobalTheory.CompHS.WeightGapAntitone

theorem GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) (P : WtPar Dw) (j : ℕ), (∀ τ, StrictAnti (P.u₁ τ)) →
    2 ≤ GlobalTheory.FlagTan.dimFlag Dw + j → 1 ≤ Dw.p → 1 ≤ Dw.q →
    ∀ τ, Antitone (P.wt j τ) ∧ 1 ≤ GlobalTheory.CompHS.gap (P.wt j τ) (Dw.p - 1) := by
  intro E _ _ _ H Dw P j hu hD hp hq τ
  have key : ∀ k (h : k + 1 < Dw.p + Dw.q), 1 ≤ gap (P.wt j τ) k := by
    intro k h
    have hr := (P.gap_rem τ k).1
    have hu1 : P.u₁ τ ⟨k + 1, h⟩ < P.u₁ τ ⟨k, by omega⟩ := hu τ (Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
    have hk : -2 ≤ FlagTan.kap Dw τ ⟨k, by omega⟩ - FlagTan.kap Dw τ ⟨k + 1, h⟩ := by
      simp only [FlagTan.kap, Fin.val_mk]
      split_ifs <;> push_cast <;> omega
    rw [gap, dif_pos h] at hr ⊢
    simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply] at hr ⊢
    simp only [nsmul_eq_mul] at hr ⊢
    have hD' : (2 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + (j : ℤ) := by exact_mod_cast hD
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + j - 2 by linarith)
      (show (0 : ℤ) ≤ P.u₁ τ ⟨k, by omega⟩ - P.u₁ τ ⟨k + 1, h⟩ - 1 by linarith)]
  exact ⟨WeightGapAntitone.antitone_of_gap_nonneg _ fun k h => by have := key k h; omega, key _ (by omega)⟩

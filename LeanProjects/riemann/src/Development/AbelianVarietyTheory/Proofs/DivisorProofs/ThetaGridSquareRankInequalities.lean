import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.Div.SquareRanks

theorem square_ranks : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (i j : Fin D.R.m),
    (spW₁ G i j).rank < (spW G i j).rank ∧ Even ((spW G i j).rank + (spW₁ G i j).rank) ∧
    2 * ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) + 1 < ((spW G i j).rank - (spW₁ G i j).rank) / 2 ∧
    2 * ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) + 1 < (spW₁ G i j).rank := by
  intro D T L sc G μ₀ hL i j
  have r : ∀ a b, a ≤ D.R.m → b ≤ D.R.m → (G.V (.grid a b)).rank = rankV D a b :=
    fun a b ha hb => (node_isV G hL (X := .grid a b) ⟨ha, hb⟩).rank
  have hi := i.2
  have hj := j.2
  have e1 : (spW G i j).rank = rankV D (i + 1) (j + 1) := r _ _ (by omega) (by omega)
  have e2 : (spW₁ G i j).rank = rankV D i j := r _ _ (by omega) (by omega)
  have e3 : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  rw [e1, e2, e3]
  have h0 : D.R.r ≤ rankV D i j := by unfold rankV; omega
  have ht := D.R.t_odd
  have hk := D.R.k_even
  have hm := D.R.m_even
  have h3 := D.R.three_m_lt_t
  have h4 := D.R.m_add_three_le_k
  have h5 := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hs : sLen D = D.R.r + 6 := rfl
  obtain ⟨t', ht'⟩ := ht
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  refine ⟨by omega, ?_, by omega, by omega⟩
  rw [Nat.even_iff]
  omega

end GlobalTheory.Div.SquareRanks

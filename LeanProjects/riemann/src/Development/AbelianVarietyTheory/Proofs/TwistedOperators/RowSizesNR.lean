import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodsOnLineOfInvLine

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

def rowSizes (D : D7) : Sizes where
  k := D.R.k
  m := D.R.m
  s := sLen D
  t := D.R.t
  k_pos := by have := D.R.m_add_three_le_k; omega
  k_even := D.R.k_even
  m_pos := by have := D.R.two_le_m; omega
  m_even := D.R.m_even
  s_odd := odd_sLen D
  t_odd := D.R.t_odd

theorem rowSizes_nR (D : D7) (j : ℕ) : (rowSizes D).nR j = rankX D j := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  simp only [Sizes.nR, rowSizes, rankX, rankP, nRk, sLen, Ranks.r]
  zify [show 1 ≤ D.R.k + D.R.m by omega, show 1 ≤ D.R.k + D.R.m - 1 + 6 by omega] at *
  push_cast
  ring_nf

theorem rowSizes_nC (D : D7) (i : ℕ) : (rowSizes D).nC i = rankV D i D.R.m := by
  simp only [Sizes.nC, rowSizes, rankV, Ranks.r]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_top (G : GridData L sc) {j : ℕ} (hj : j ≤ D.R.m) : (G.V (.top j)).rank = (rowSizes D).nR j := by
  rw [rowSizes_nR]
  rcases j with _ | j
  · exact ((G.sp.P_is D.R.m le_rfl).rank).trans (by simp [rankX])
  · exact (G.sp.X_is (j + 1) (by omega) hj).rank

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem rank_gridM (G : GridData L sc) {i : ℕ} (hi : i ≤ D.R.m) : (G.V (.grid i D.R.m)).rank = (rowSizes D).nC i := by
  rw [rowSizes_nC]
  rcases i with _ | i
  · show (columnBlock L D.R.m).sp.rank = _
    rw [colY_m]
    exact D.sp.X'_rank.trans (by simp [rankV, Ranks.rankX'])
  · exact (G.sp.V_is (i + 1) D.R.m (by omega) hi le_rfl).rank

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

def rowEntries (D : D7) (C : ℝ) (τ : D.what₂.Tau) : Entries (rowSizes D) where
  a l := (num D C τ).a l
  c i := (num D C τ).cen (i + 1)
  v i := (num D C τ).v (i + 2)
  u i := (num D C τ).vHalf (i + 2)
  b j := (num D C τ).b (j + 1)
  e j := (num D C τ).e (j + 1)

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def trCol (G : GridData L sc) (j : Fin D.R.m) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ]
      Pol D.what₂.Tau ((rowSizes D).nR j) ((rowSizes D).nR (j + 1)) :=
  MvPolynomial.rename fun x => (x.1, Fin.cast (rank_top G (by omega)) x.2.1, Fin.cast (rank_top G j.2.le) x.2.2)

def trRow (G : GridData L sc) (i : Fin D.R.m) :
    PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank →ₐ[ℂ]
      Pol D.what₂.Tau ((rowSizes D).nC i) ((rowSizes D).nC (i + 1)) :=
  MvPolynomial.rename fun x => (x.1, Fin.cast (rank_gridM G (by omega)) x.2.2, Fin.cast (rank_gridM G i.2.le) x.2.1)

example (G : GridData L sc) : PolCol G = ∀ j : Fin D.R.m, PolF D (G.V (.top ((j : ℕ) + 1))).rank (G.V (.top j)).rank := rfl
example (G : GridData L sc) : PolRow G = ∀ i : Fin D.R.m, PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid ((i : ℕ) + 1) D.R.m)).rank := rfl

end GlobalTheory.RowReal

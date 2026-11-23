import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ChainMatrices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesExistG2OfStandardLattices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mi Formalism.IndefR.Seed.Frm IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VertexFromTransport

theorem vertexAt_of_levTransport : ∀ {D : D7} {T : Type} (L : LevCh D T), (∀ PP, PP ∈ L.Pg ↔ ∃ l, L.C.P.Div l PP) →
    ∀ i : Fin D.R.m, GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.Transport L.Pg (Wc D i) (Yc D 0) (L.βW i) (L.βY 0) →
    ∃ (eW : Fin (D.sp.Y 0).rank ≃ Fin (D.sp.W ((i : ℕ) + 1)).rank)
      (ι : GL (Fin (D.sp.W ((i : ℕ) + 1)).rank) (Formalism.IndefR.Lev.EAf D)),
      VertexAt ((i : ℕ) + 1) (betaYOf L.βY 0) (L.βW i) eW ι L.Pg := by
  intro D T L _ i ht
  have hr : (D.sp.Y 0).rank = (D.sp.W ((i : ℕ) + 1)).rank := by
    rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.W_rank _ (by omega) (by omega)]
    simp [Ranks.rankY]
  exact GlobalTheory.NormalFramesLevels.vertexAt_of_transport L.Pg _ hr _ _
    (GlobalTheory.NormalFramesLevels.transport_betaYOf L.Pg (Wc D i) (L.βW i) L.βY ht)

end GlobalTheory.VertexFromTransport

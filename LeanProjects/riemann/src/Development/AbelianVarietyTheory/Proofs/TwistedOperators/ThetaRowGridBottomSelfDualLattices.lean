import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceLevelOfEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLatticeCongruenceMemConjugateIdealInfStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusInfConjLeSpanTypePrimesProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardNegativeSignsDiagonalFrameEqSignatureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BottomGrid

theorem bottom : All fun {D} _ {L} _ {G} _ _ => IsSelfDualC (Yc D 0) (L.ΛY 0) ∧ IsSelfDualC (G.V (.core 0)) (G.Λ (.core 0)) ∧ G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) ∧ zv G.sp.dec0 ∈ G.Λ (.core 0) ∧ (∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈ G.levCong (.core 0) → k ∈ levRow L) ∧ (Yc D 0).rank = D.R.r ∧ (G.V (.core 0)).rank = D.R.r + 1 ∧ ∀ (A : Fr (Yc D 0)) τ, (Finset.univ.filter fun a => A.ε τ a = false).card ≤ D.R.m := by
  intro D _ T L μ0 hL sc G W M _
  have hY : (⟨Yc D 0, L.ΛY 0⟩ : LSp D).IsV (Node.rank D (.grid 0 0)) (Node.neg D.R.m (.grid 0 0)) :=
    node_isV G hL (X := .grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hP := G.sp.P_is 0 (Nat.zero_le _)
  refine ⟨hY.sd, hP.sd, G.sp.lat0, ?_, ?_, ?_, ?_, ?_⟩
  · show zv G.sp.dec0 ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨0, Submodule.zero_mem _, fun _ => 1, fun p => ?_, ?_⟩
    · exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
    · funext i
      simp [zv, Matrix.mulVec, dotProduct]
  · intro k hk hfin
    have h1 : Lev.finE (Yc D 0) k ∈ congLev D.sp.cm (Yc D 0).gram (L.ΛY 0) G.modul := by
      refine GlobalTheory.T.congruence_level_of_embedding G.sp.dec0 (L.ΛY 0) (fun _ => 1) G.modul k ?_
      have e : G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) := G.sp.lat0
      have := hfin
      unfold GridData.levCong at this
      rw [e] at this
      exact this
    have h2 := GlobalTheory.T.unitaryLatticeCongruence_mem_conjugateIdeal_inf (Yc D 0) (L.ΛY 0) hY.sd _ _ h1
    exact Subgroup.mem_inf.2 ⟨hk, congLev_mono (GlobalTheory.T.modulus_inf_conj_le_span_typePrimes_product G) h2⟩
  · simpa [Node.rank, rankV] using hY.rank
  · simpa [Node.rank, rankP, nRk] using hP.rank
  · intro A τ
    rw [GlobalTheory.T.card_negativeSigns_diagonalFrame_eq_signature _ hY.sigOK A τ, hY.sig]
    simp only [Node.neg, Nat.sub_zero]
    exact Nat.div_le_self _ _
end GlobalTheory.BottomGrid

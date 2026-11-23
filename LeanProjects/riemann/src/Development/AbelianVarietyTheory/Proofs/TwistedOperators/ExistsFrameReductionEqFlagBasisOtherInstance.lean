import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameLiftingPrescribedReductionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFrameIntegralityConditionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableDiagonalModSmallStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingVectorsIntegralInFrameStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagPairingTableIdempotentComponentNeOneStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem cT_mul_entry {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (U J W : Matrix (Fin n) (Fin n) A) (a b : Fin n) :
    (Formalism.UG.cT σ U * J * W) a b = Formalism.UG.hform σ J (fun i => U i a) (fun i => W i b) := by
  unfold Formalism.UG.cT Formalism.UG.hform
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply]
  exact Finset.sum_comm

theorem over_g {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) {Q : Pl D.host.E}
    (hQ : Q ∈ R.Pg) : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
  obtain ⟨k, hk⟩ := (hL.Pg Q).1 hQ
  have hmem : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (Q.under (𝓞 D.host.K)).asIdeal := by
    rw [show Q.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact R.C.P.pb_over k
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem
  rw [Nat.cast_mul]
  fin_cases k
  · exact Ideal.mul_mem_right _ _ hmem
  · exact Ideal.mul_mem_left _ _ hmem

theorem exists_frame_redIs : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL _
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    rw [show (Yc D 0).rank = D.R.rankY 0 from D.sp.Y_rank 0 (Nat.zero_le _)]
    have hm := D.R.m_even
    have h2 := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rankY Formalism.BasicNotions.Ranks.rS Formalism.BasicNotions.Ranks.r
    obtain ⟨c, hc⟩ := hm
    omega
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.StdFrames.exists_base (Yc D 0)
  have hG := (GlobalTheory.StdFrames.unimod_of_isSD (GlobalTheory.StdFrames.isSD_one hβ₀)).1
  have hint := fun PP i j => GlobalTheory.T.flagPairingVectors_integral_inFrame X h β₀ hβ₀ PP i j
  have hdet : ∀ Q ∈ R.Pg,
      Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (flagAt X h Q)).det) = 1 := by
    intro Q hQ
    have hg := over_g R hL hQ
    refine GlobalTheory.T.standard_frame_integrality_conditions β₀ (GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram) (colMat (pairAt X h Q))
      (colMat (flagAt X h Q)) Q (fun a => sgnD D.R.rS D.R.k a) hG (fun i j => (hint Q i j).2)
      (fun i j => (hint Q i j).1) ?_ ?_
    · intro a
      unfold sgnD
      split_ifs <;> simp
    · intro a b
      rw [cT_mul_entry]
      change SmallAt Q (hY D (pairAt X h Q a) (flagAt X h Q b) - _)
      by_cases hc : GlobalTheory.StdFrames.cpt Q (ewT X h) = 1
      · rw [pairAt, flagAt, if_pos hc, if_pos hc]
        exact GlobalTheory.T.flagPairingTable_diagonal_modSmall (hY D) (SmallAt Q) D.R.rS D.R.k _ hn _ _ _ _ _ (GlobalTheory.T.flagPairingTable_idempotentComponent_one X h Q hg hc) a b
      · rw [pairAt, flagAt, if_neg hc, if_neg hc]
        exact GlobalTheory.T.flagPairingTable_diagonal_modSmall (hY D) (SmallAt Q) D.R.rS D.R.k _ hn _ _ _ _ _ (GlobalTheory.T.flagPairingTable_idempotentComponent_ne_one X h Q hg hc) a b
  obtain ⟨β, hβ, hred⟩ := GlobalTheory.T.exists_frame_lifting_prescribed_reductions β₀ R.Pg (flagAt X h) (fun Q _ i j => (hint Q i j).1) hdet
  refine ⟨β, ?_, hred⟩
  rw [hβ₀, ← hβ]
  exact GlobalTheory.StdFrames.isFrame_lat β

end GlobalTheory.SeeConjRead

end

import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TowerIsChain
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfExpMulZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTupChars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Formalism.LocalRingCardinality.PosOfIsomEmb
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerChain

theorem under_mem_S (D : D7) (W : GlobalTheory.Core.Rk.Tower D) (h : W.Is) (k : Fin 2) (P : Pl D.host.E)
    (hk : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : P.under (𝓞 D.host.F) ∈ (comOf W).S := by
  classical
  unfold Com.S
  rw [Finset.mem_image]
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D W.C.P k P hk with h1 | ⟨P', h1, hc⟩
  · exact ⟨P, (h.chars.Pg P).2 ⟨k, h1⟩, rfl⟩
  · refine ⟨P', (h.chars.Pg P').2 ⟨k, h1⟩, ?_⟩
    ext x
    show algebraMap _ _ x ∈ P'.asIdeal ↔ algebraMap _ _ x ∈ P.asIdeal
    rw [hc, Formalism.L2.Col.mem_conjIdeal]
    have : Formalism.L2.Col.cO D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap _ _ x := by
      apply RingOfIntegers.ext
      exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
    rw [this]

theorem com_is (D : D7) (W : GlobalTheory.Core.Rk.Tower D) (h : W.Is) (hQ : W.Q () = ∅) : (comOf W).Is := by
  have hL := h.chars
  have hμ : ∀ j : Fin D.R.m, ChrEq (W.toLevCh.mu () ((j : ℕ) + 1)) (W.C.mu0 j) := fun j => by
    have := GlobalTheory.Mem.TupChar.chrEq_mul (hL.mu0 j) (hL.xi ())
    rw [hL.xi_base, mul_one] at this
    exact this
  refine ⟨h.inf, h.std, ⟨hL.eta.1, GlobalTheory.Mem.TupChar.unramEverywhere hL.eta W.C.isEta.unr, GlobalTheory.HeckeCharacterRestriction.resEta_eta hL, fun τ => ?_, fun j hj => ?_⟩,
    fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hL.chi j⟩, ?_⟩
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, W.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact ⟨GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL () ⟨i, by omega⟩, GlobalTheory.HeckeCharacterRestriction.resEta_mu hL () ⟨i, by omega⟩⟩
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (W.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    exact h1
  · exact (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((W.C.isMu0 j).unr w fun k hk => hw (under_mem_S D W h k w hk))
  · obtain ⟨e, he, -⟩ := h.vX.2
    rw [hQ] at he
    exact ⟨e, by simp only [Finset.union_empty] at he; exact he⟩

theorem Q_eq_empty (D : D7) (W : GlobalTheory.Core.Rk.Tower D) (h : W.Is) : W.Q () = ∅ := by
  ext PP
  simp only [Finset.notMem_empty, iff_false]
  intro hP
  have := (h.chars.Q_ram () PP).2 (Or.inl hP)
  rw [h.chars.xi_base] at this
  exact this fun x _ => rfl

theorem stages (D : D7) (W : GlobalTheory.Core.Rk.Tower D) (h : W.Is) (hQ : W.Q () = ∅) :
  (∀ j < D.R.m, (stageY W j).Is (comOf W) j) ∧ (stageX W).Is (comOf W) D.R.m := by
  refine ⟨fun j hj => ?_, ?_⟩
  · have hm : min j D.R.m = j := min_eq_left hj.le
    obtain ⟨c, hc⟩ := h.chars.βY j hj
    have hν : (W.νY j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (W.fdY j) (W.νY j) := by
      by_cases h1 : j + 1 < D.R.m
      · exact ⟨(h.νY j h1).1.1, (h.νY j h1).2⟩
      · have : j = D.R.m - 1 := by omega
        subst this
        exact ⟨h.νY'.1.1, h.νY'.2⟩
    refine ⟨?_, D.sp.Y_sig _, fun τ => ?_, ?_, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1, ⟨_, hc, fun P hP hN => hP ?_⟩, ⟨r_le_Y j, W.xiR (), ?_⟩, hν.1, hν.2⟩
    · show (D.sp.Y (min j D.R.m)).rank = _
      rw [D.sp.Y_rank _ (min_le_right _ _), hm]
    · show (D.sp.Y (min j D.R.m)).sig τ = _
      rw [D.Y_sigval _ (min_le_right _ _), hm]
    · show parB _ (min j D.R.m) = _
      rw [hm]
    · push_cast at hN
      have := P.isPrime.mem_of_pow_mem _ hN
      rcases P.isPrime.mem_or_mem this with h0 | h0
      · exact under_mem_S D W h 0 P h0
      · exact under_mem_S D W h 1 P h0
    · show Lev.datY _ _ _ _ _ _ (W.Q ()) _ _ _ _ = _
      rw [hQ]; rfl
  · obtain ⟨c, hc⟩ := h.chars.βX
    refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_, rfl, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1, ⟨_, hc, fun P _ hN => ?_⟩, ⟨r_le_X, W.xiR (), ?_⟩, h.νX.1.1, h.νX.2⟩
    · show D.sp.X'.sig τ = _
      rw [D.X'_posDef τ, D.sp.X'_rank]; simp [sigYD, Ranks.rankY, Ranks.rankX']
    · rw [one_pow, Nat.cast_one] at hN
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hN)
    · show Lev.datY _ _ _ _ _ _ (W.Q ()) _ _ _ _ = _
      rw [hQ]; rfl

theorem tower_isChain (D : D7) (W : GlobalTheory.Core.Rk.Tower D) (h : W.Is) : TowerIsChain W := by
  have hQ := Q_eq_empty D W h
  refine ⟨com_is D W h hQ, (stages D W h hQ).1, (stages D W h hQ).2, fun k hk => ⟨h.ωY k hk, ⟨W.xiR (), W.vac k, ?_⟩, h.ptY k hk, h.ItY k hk, h.ioY k (by omega)⟩, ⟨h.ωX, ⟨W.xiR (), W.vacX, ?_⟩, h.ptX, h.ItX, h.ioX⟩⟩
  · have := h.vY k hk; rw [hQ] at this; exact this
  · have := h.vX; rw [hQ] at this; exact this

end GlobalTheory.TowerChain

end

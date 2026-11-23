import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.TieSame

theorem bsH_val_congr {e e' : Formalism.HC.Frame} (he : e = e') (h t : e.A) (h' t' : e'.A)
    (hh : h.val = h'.val) (ht : t.val = t'.val) : (Arith.bsH h t).val = (Arith.bsH h' t').val := by
  subst he
  have h1 := Formalism.HC.Frame.A.val_injective _ hh
  have h2 := Formalism.HC.Frame.A.val_injective _ ht
  rw [h1, h2]

theorem mem_iff_val_mem {e : Formalism.HC.Frame} (T : Finset e.A) (t : e.A) :
    t ∈ T ↔ t.val ∈ T.image Formalism.HC.Frame.A.val := by
  constructor
  · intro h; exact Finset.mem_image_of_mem _ h
  · intro h
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
    rwa [← Formalism.HC.Frame.A.val_injective _ hst]

theorem kapISet_congr {D D' : D7} (L : SizeData₂ D) (L' : SizeData₂ D') (hR : D.R = D'.R) (hs : L.sc = L'.sc) (hS : L.Sc = L'.Sc)
    (K : G.Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    G.kapISet L K p n' TT a b = G.kapISet L' K p n' TT a b := by
  have hk : D.R.k = D'.R.k := by rw [hR]
  have hc : G.cG L = G.cG L' := by unfold G.cG; rw [hS]
  have hD : G.DIf K L p n' = G.DIf K L' p n' := by unfold G.DIf; rw [hs, hk]
  have h6 : G.c6f K L p n' = G.c6f K L' p n' := by unfold G.c6f; rw [hD, hs, hk, hc]
  have ht : G.tIf K L p n' TT a b = G.tIf K L' p n' TT a b := by unfold G.tIf; rw [h6, hs, hk, hc]
  unfold G.kapISet
  rw [hc, hD, ht, hk]

theorem nonempty_place (D : D7) : Nonempty D.what₂.places.Pl := by
  haveI := D.nfLL
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.what₂.LL)
  exact ⟨D.plEq.symm ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩

theorem off_lift {C : FC} {cD ch : ℝ} (p : Pt C) (hv : Val C cD ch p.L) (j : ℕ) (hj : j ∈ SizeData₂.lifts p.D) (t : G.HH p.D) :
    p.ta.Gx.off j (false, t) =
      (if t ∈ p.D.host.TT then ((⌊p.L.sc.b' / p.L.sc.x⌋ : ℤ) : ℝ) else ((⌈p.L.sc.w'' p.D.R.n⌉ : ℤ) : ℝ)) +
        ((j - 1 : ℕ) : ℝ) * (h0v p.L.sc ch : ℝ) + (h0v p.L.sc ch : ℝ) / 2 := by
  obtain ⟨w⟩ := nonempty_place p.D
  have hP := factPlaces p.D.R.toFrame
  have hmem : p.D.R.tau1 t ∈ p.D.R.Psi := (hP.1 _).2 (Or.inl ⟨t, rfl⟩)
  set τ := p.D.eTau.symm ⟨_, hmem⟩ with hτ
  have hτe : (p.D.eTau τ : p.D.R.GG) = p.D.R.tau1 t := by rw [hτ, Equiv.apply_symm_apply]
  have hf := (p.ta.fills w).1 j hj τ (false, t) (by rw [hτe]; rfl)
  have hjm : j - 1 < p.D.R.m := by
    have := Finset.mem_Icc.1 hj
    omega
  obtain ⟨-, -, ⟨b1, hb, htop, -, hthin⟩, -⟩ := hv.hc
  obtain ⟨hb1, hb2⟩ := hb τ ⟨j - 1, hjm⟩
  unfold wj at hf
  rw [dif_pos hjm, hb2, hb1] at hf
  unfold G.fill at hf
  by_cases ht : t ∈ p.D.host.TT
  · have h1 := htop τ ⟨t, ht⟩ hτe
    rw [if_pos ⟨rfl, ht⟩, h1] at hf
    rw [if_pos ht]
    unfold G.bL at hf
    rw [dif_pos ht] at hf
    push_cast at hf ⊢
    linarith
  · have h1 := hthin τ (by
      show p.D.host.IsThin (p.D.eTau τ : p.D.R.GG)
      rw [hτe]
      refine ⟨hmem, ?_, ?_⟩
      · intro h
        obtain ⟨s, hs, hst⟩ := Finset.mem_image.1 h
        have : s = t := p.D.R.iota_bijective.1 (congrArg Prod.snd hst)
        exact ht (this ▸ hs)
      · intro h
        obtain ⟨s, -, hst⟩ := Finset.mem_image.1 h
        exact hP.2 _ _ hst.symm)
    rw [if_neg (fun h => ht h.2), h1] at hf
    rw [if_neg ht]
    push_cast at hf ⊢
    linarith

theorem same_of_from : ∀ (C : FC) (cD ch : ℝ) (p p' : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 u0' : ℕ), p.L.sc = p'.L.sc → Val C cD ch p.L → Val C cD ch p'.L → p.From H a b c u0 → p'.From H a b c u0' → CanonInst p.ta.Gx → CanonInst p'.ta.Gx → p.Same p' := by
  intro C cD ch p p' R H a b M c u0 u0' hs hv hv' hF hF' hC hC'
  have hQS := hF.QS_eq.trans hF'.QS_eq.symm
  have hart := hF.art_eq.trans hF'.art_eq.symm
  have hrd := hF.rd_eq.trans hF'.rd_eq.symm
  obtain ⟨hR, hTT, hT2, hq, hd, hg, hp1, hp2, -, -, hh, hw, -⟩ := hF
  obtain ⟨hR', hTT', hT2', hq', hd', hg', hp1', hp2', -, -, hh', hw', -⟩ := hF'
  have hRR : p.D.R = p'.D.R := hR.trans hR'.symm
  have hT : p.D.host.TT.image Formalism.HC.Frame.A.val = p'.D.host.TT.image Formalism.HC.Frame.A.val := hTT.trans hTT'.symm
  have hSc : p.L.Sc = p'.L.Sc := by rw [p.L.Sc_eq, p'.L.Sc_eq, hv.Del_eq, hv'.Del_eq, hs, hRR]
  have hmem : ∀ (t : G.HH p.D) (t' : G.HH p'.D), t.val = t'.val → (t ∈ p.D.host.TT ↔ t' ∈ p'.D.host.TT) := by
    intro t t' htt
    rw [mem_iff_val_mem p.D.host.TT t, mem_iff_val_mem p'.D.host.TT t', hT, htt]
  have hn : p.D.R.n = p'.D.R.n := by rw [hRR]
  refine ⟨hRR, hT, hT2.trans hT2'.symm, hq.trans hq'.symm, hd.trans hd'.symm, hg.trans hg'.symm, hp1.trans hp1'.symm,
    hp2.trans hp2'.symm, ?_, hSc, fun l => (hh l).trans (hh' l).symm, ?_, ?_, ?_, ?_, ?_, hQS, hart, hrd⟩
  · rw [hv.eta_eq, hv'.eta_eq, hs, hRR]
  · intro h t h' t' e1 e2
    rw [hC.1, hC'.1]
    exact bsH_val_congr (by rw [hRR]) h t h' t' e1 e2
  · intro j t t' htt
    have hm := hmem t t' htt
    have hl : SizeData₂.lifts p.D = SizeData₂.lifts p'.D := by unfold SizeData₂.lifts; rw [hRR]
    by_cases hj : j ∈ SizeData₂.lifts p.D
    · rw [off_lift p hv j hj t, off_lift p' hv' j (hl ▸ hj) t', hs, hn]
      by_cases ht : t ∈ p.D.host.TT
      · rw [if_pos ht, if_pos (hm.1 ht)]
      · rw [if_neg ht, if_neg (fun h => ht (hm.2 h))]
    · rw [hC.2 j hj t, hC'.2 j (hl ▸ hj) t', hs, hn]
      by_cases ht : t ∈ p.D.host.TT
      · rw [if_pos ht, if_pos (hm.1 ht)]
      · rw [if_neg ht, if_neg (fun h => ht (hm.2 h))]
  · funext l n' TT a' b'
    rw [p.xa.ex.kapI_def l n' TT a' b', p'.xa.ex.kapI_def l n' TT a' b', kapISet_congr p.L p'.L hRR hs hSc]
  · funext l
    rw [p.xa.ex.ep_def l, p'.xa.ex.ep_def l, hs, hRR]
  · intro t t' htt
    have hlt : (t : p.D.R.A).val < R.ord := by
      have := Formalism.HC.Frame.A.val_lt (t : p.D.R.A)
      rwa [show R.ord = p.D.R.ord by rw [hR]]
    have hv0 : (R.ofNat (t : p.D.R.A).val).val = (t : p.D.R.A).val :=
      R.toFrame.val_ofNat_of_lt hlt
    obtain ⟨e1, e2⟩ := hw t _ hv0.symm
    obtain ⟨e3, e4⟩ := hw' t' _ (htt.symm.trans hv0.symm)
    exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩

end GlobalTheory.EX.TieSame

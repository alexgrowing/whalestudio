import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpWindowAndBlockExponentOfEmbeddings
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankLeOfSubsetClosureRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFinrankKs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionOfLocalTheoremHypWStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TheoremBTB

theorem localTB : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ), LocalSituation.Conclusion4 D HW F → (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (h : Good (D.nbr i w hw).Kw 1 C.LL), EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL h) ((F (D.nd.l i)).E (D.nbr i w hw).Kw 1 C.LL h).tie) → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := GlobalTheory.T.localCondition_of_local_theorem_hypW

theorem l_ge_three (D : D7) (i : D.nd.Loc) (hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) : 3 ≤ D.nd.l i := by
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have htr : 1 ≤ D.R.t * D.R.r := Nat.mul_pos ht1 hr1
  rcases hl with h | h <;> rw [h]
  · have := D.host.qd_big.1; nlinarith
  · have := D.host.qd_big.2; nlinarith

theorem jointCond_at_qd (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool)
    (h0 : EmbeddingTypeJumps.Conclusion0 D) (hJump : EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂) (hPar : EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂) (i : D.nd.Loc) (hQ : EmbeddingTypeJumps.AtQD i)
    (π : D.nd.X i) :
    JointConditionTameBound D HW F i (r i) π ⌊2 * large₂.sc.b⌋₊ ⌊2 * large₂.sc.b⌋₊
      (GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV)) := by
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hQ.1.1
  have hl3 := l_ge_three D i hl
  refine ⟨by omega, fun w hw => ?_⟩
  obtain ⟨-, hK1, -, hdegK⟩ := h0 i hl w hw
  refine ⟨GlobalTheory.BridgeInertia.inertEq D i w hw, hK1, fun C hs Y hc hY => ?_⟩
  have hs1 : (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).W.s = 1 :=
    (HW (D.nd.l i)).W_s _ 1 _ hs
  have hell : LocalSituation.ell (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) = D.nd.l i :=
    (D.loc (D.nd.l i)).PD_p _
  haveI : CharZero (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).Qp :=
    inferInstanceAs (CharZero ℚ_[D.nd.l i])
  haveI : FiniteDimensional (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).Qp
      (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).K := (D.nbr i w hw).Kw.2
  have hcard : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    GlobalTheory.HubLoc.card_emb _ _ fun τ x => C.le ((D.nbr i w hw).LL_split τ x)
  have hdeg := GlobalTheory.bridge_finrank_le D i w hw
  obtain ⟨hv1, -⟩ := GlobalTheory.HubLoc.padicValNat_finrank_Ks (D.nd.l i) (D.nbr i w hw).Kw
  have hK0 : Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 ≠ 0 := Module.finrank_pos.ne'
  have hgK : LocalSituation.gK (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) = 0 := by
    unfold LocalSituation.gK
    rw [hs1, hell]
    show padicValNat (D.nd.l i) (Module.finrank ℚ_[D.nd.l i] ↥(Ks (D.nbr i w hw).Kw 1)) -
      padicValNat (D.nd.l i) (Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1) = 0
    have hpos : (D.nd.l i - 1) / 2 ≠ 0 := by omega
    have hv : padicValNat (D.nd.l i) ((D.nd.l i - 1) / 2) = 0 :=
      padicValNat.eq_zero_of_not_dvd fun h => by
        have := Nat.le_of_dvd (by omega) h
        omega
    rw [hdegK, padicValNat.mul hpos hK0, hv, zero_add, Nat.sub_self]
  have hvd : ∀ m : ℕ, 0 < m → LocalSituation.vdegMs (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) m = m - 1 := by
    intro m hm
    unfold LocalSituation.vdegMs
    rw [hs1, hell]
    exact hv1 m hm
  have hb := hPar
  unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hb
  have hη := large₂.etaSz_pos
  have hS := large₂.Sc_pos
  have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
  have hfl : ∀ z : ℤ, (z : ℝ) ≤ 2 * large₂.sc.b → z ≤ (⌊2 * large₂.sc.b⌋₊ : ℤ) := by
    intro z hz
    rcases le_or_gt z 0 with h | h
    · exact h.trans (Int.natCast_nonneg _)
    · have h2 : ((z.toNat : ℕ) : ℝ) ≤ 2 * large₂.sc.b := by
        rw [show ((z.toNat : ℕ) : ℝ) = (z : ℝ) by exact_mod_cast Int.toNat_of_nonneg h.le]; exact hz
      have := Nat.le_floor h2
      omega
  have ht : D.R.t ≤ ⌊2 * large₂.sc.b⌋₊ := by
    have := hfl (D.R.t : ℤ) (by push_cast; linarith)
    omega
  have key := GlobalTheory.HubLoc.window_and_cTB_of_jumps_at_embeddings
    (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) Y ⌊2 * large₂.sc.b⌋₊ D.R.nV (4 * D.R.n) D.R.t
    hs1 hcard hdeg hgK (hvd _ (by unfold LocalSituation.mN; omega)) ht (fun τ => by
      obtain ⟨s, Jc, Jl, hs1', hs2', hJc, hJl, hlow, hcl, -, -, hiff⟩ := hJump i hQ w hw C τ
      classical
      refine ⟨Jc ∪ Jl ∪ Finset.Ico (0 : ℤ) D.R.t, ?_, ?_, fun a ha => ?_⟩
      · calc (Jc ∪ Jl ∪ Finset.Ico (0 : ℤ) D.R.t).card ≤ (Jc ∪ Jl).card + (Finset.Ico (0 : ℤ) D.R.t).card :=
              Finset.card_union_le _ _
          _ ≤ Jc.card + Jl.card + (Finset.Ico (0 : ℤ) D.R.t).card := by
              have := Finset.card_union_le Jc Jl; omega
          _ = D.R.nV := by
              rw [hJc, hJl, Int.card_Ico]
              unfold Ranks.nV Ranks.r
              have := D.R.m_add_three_le_k
              simp only [sub_zero, Int.toNat_natCast]
              omega
      · intro u hu
        simp only [Finset.mem_union, Finset.mem_Ico] at hu
        rcases hu with (hu | hu) | hu
        · rcases hcl with hc' | hc'
          · obtain ⟨a1, a2⟩ := hc' u hu
            have hs0 : (0 : ℝ) < s := by linarith
            constructor
            · have : (0 : ℤ) < s := by exact_mod_cast hs0
              omega
            · exact hfl (u + 1) (by push_cast; linarith)
          · obtain ⟨a1, a2⟩ := hc' u hu
            have hs0 : (0 : ℝ) < s := by linarith
            constructor
            · have := hfl (-u) (by push_cast; linarith)
              omega
            · have : (0 : ℤ) < s := by exact_mod_cast hs0
              omega
        · obtain ⟨hb', -, -, -⟩ := hlow u hu
          rcases hb' with ⟨a1, a2⟩ | ⟨a1, a2⟩
          · constructor
            · have := hfl (-u) (by push_cast; linarith)
              omega
            · omega
          · constructor
            · omega
            · exact hfl (u + 1) (by push_cast; linarith)
        · constructor
          · omega
          · omega
      · have := (hiff π a).1 (hY τ a ha)
        simp only [Finset.mem_union, Finset.mem_Ico]
        tauto)
  refine ⟨key.1, fun e he => (key.2 e he).trans (le_of_eq ?_)⟩
  rw [hell]

theorem cBnum_le (l t n r : ℕ) (b : ℝ) (hl : 3 ≤ l) (ht : 1 ≤ t) (hn : 1 ≤ n) (hr : 1 ≤ r) (hb : 1 < b)
    (hL : 1 < Real.log b) :
    (GlobalTheory.HubLoc.cBnum l ⌊2 * b⌋₊ t (4 * n * (r + t)) : ℝ) ≤
      60 * (t : ℝ) * ((2 * n : ℕ) : ℝ) * ((r : ℝ) + (t : ℝ)) * Real.log b := by
  set L := Real.log b with hLdef
  set lam := Nat.log l (2 * ⌊2 * b⌋₊) with hlam
  have hfl2 : 2 ≤ ⌊2 * b⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hpow : l ^ lam ≤ 2 * ⌊2 * b⌋₊ := Nat.pow_log_le_self l (by omega)
  have h3pow : 3 ^ lam ≤ l ^ lam := Nat.pow_le_pow_left hl lam
  have hfb : ((⌊2 * b⌋₊ : ℕ) : ℝ) ≤ 2 * b := Nat.floor_le (by linarith)
  have h3R : (3 : ℝ) ^ lam ≤ 4 * b := by
    have : ((3 ^ lam : ℕ) : ℝ) ≤ ((2 * ⌊2 * b⌋₊ : ℕ) : ℝ) := by exact_mod_cast h3pow.trans hpow
    push_cast at this
    linarith
  have hlog3 : 1 ≤ Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  have hlamL : (lam : ℝ) ≤ 4 * L := by
    have h1 : Real.log ((3 : ℝ) ^ lam) ≤ Real.log (4 * b) := Real.log_le_log (by positivity) h3R
    rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : (lam : ℝ) ≤ (lam : ℝ) * Real.log 3 := by
      have : (0 : ℝ) ≤ lam := by positivity
      nlinarith
    linarith
  unfold GlobalTheory.HubLoc.cBnum
  rw [← hlam]
  push_cast
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlam0 : (0 : ℝ) ≤ lam := by positivity
  set P : ℝ := (t : ℝ) * (2 * n) * (r + t) with hP
  have hP1 : 1 ≤ P := by
    have : (1 : ℝ) ≤ (2 * n) * (r + t) := by nlinarith
    nlinarith
  have hA : 3 + (lam : ℝ) + 3 ≤ 10 * P * L := by nlinarith
  have hB : 4 * (t : ℝ) + 3 * t ≤ 7 * P * L := by
    have : (t : ℝ) ≤ P := by
      have : (1 : ℝ) ≤ (2 * n) * (r + t) := by nlinarith
      nlinarith
    nlinarith
  have hC : (t : ℝ) * (4 * n * (r + t) * (4 + 2 * lam)) ≤ 24 * P * L := by
    have h4 : (4 : ℝ) + 2 * lam ≤ 12 * L := by linarith
    have hq : (0 : ℝ) ≤ (t : ℝ) * (4 * n * (r + t)) := by positivity
    calc (t : ℝ) * (4 * n * (r + t) * (4 + 2 * lam)) = ((t : ℝ) * (4 * n * (r + t))) * (4 + 2 * lam) := by ring
      _ ≤ ((t : ℝ) * (4 * n * (r + t))) * (12 * L) := mul_le_mul_of_nonneg_left h4 hq
      _ = 24 * P * L := by rw [hP]; ring
  have hPL : 0 ≤ P * L := by positivity
  nlinarith

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∃ cB : ℕ, TruncatedSeriesCountingIdentities.admTB i (r i) π cB ∧ (cB : ℝ) ≤ 60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b := by
  intro D HW F r ρ large₂ ep h0 _h1 hW hTB hJump _hFon _hG2 _hSet hLit hPar i hQ π _hπ
  have hl : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d := hQ.1.1
  refine ⟨GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV), ?_, ?_⟩
  · exact localTB D HW F i (r i) π _ _ _ hTB (fun w hw C h => hW i hQ w hw C h) (hLit i hQ).2.2.2.1
      (jointCond_at_qd D HW F r large₂ ep h0 hJump hPar i hQ π)
  · have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
    have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
    have hn1 : 1 ≤ D.R.n := by unfold Ranks.n; exact Nat.succ_le_of_lt (by positivity)
    have hL0 : 0 < large₂.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
    have hb1 : 1 < large₂.sc.b := by unfold Scale.b; have := Real.add_one_lt_exp (ne_of_gt hL0); linarith
    have hLb : 1 < Real.log large₂.sc.b := by
      unfold Scale.b; rw [Real.log_exp]; unfold Scale.L
      exact Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
    have key := cBnum_le (D.nd.l i) D.R.t D.R.n D.R.r large₂.sc.b (l_ge_three D i hl) ht1 hn1 hr1 hb1 hLb
    have hnV : D.R.nV = D.R.r + D.R.t := rfl
    have hf : D.R.f = 2 * D.R.n := rfl
    rw [hnV, hf]
    exact key

end GlobalTheory.TheoremBTB

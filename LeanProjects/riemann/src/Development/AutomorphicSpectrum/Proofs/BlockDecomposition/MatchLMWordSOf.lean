import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcB.F.MLM (wordLS wordUS CtStar)
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MatchWordS

open GlobalTheory.CompanionTheory.MatchWord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem isHecke_lstar {w : Pl E} {f : UL n w → ℂ} (hf : IsHecke (KL n w) f) : IsHecke (KL n w) (lstar f) := by
  refine ⟨(hf.1.comp_homeomorph (Homeomorph.inv _)).comp_left (map_zero (starRingEnd ℂ)), fun k hk x => ⟨?_, ?_⟩⟩
  · simp only [lstar, _root_.mul_inv_rev, (hf.2 _ (inv_mem hk) _).2]
  · simp only [lstar, _root_.mul_inv_rev, (hf.2 _ (inv_mem hk) _).1]

def letU (d : LocData E n) (w : Pl E) (x : ℕ × Bool × Bool) : UL n w → ℂ :=
  if x.2.2 then lstar (d.hU w x.1) else d.hU w x.1

def letL (d : LocData E n) (a : ℕ) (ha : a ≤ n) (w : Pl E) (x : ℕ × Bool × Bool) : LM d.kap a (n - a) :=
  if x.2.2 then (d.hL a ha w x.1 x.2.1).adj else d.hL a ha w x.1 x.2.1

theorem word_ct (d : LocData E n) (a : ℕ) (ha : a ≤ n) {w : Pl E} (hCt : MT.CtMul) (hSt : CtStar) (hSp : SphComm) (hE : Unr E)
    (hd : d.Ok) (hG : d.Good w) (hN : ∀ u, ‖((d.μ w u : ℂˣ) : ℂ)‖ = 1) (l : List (ℕ × Bool × Bool)) :
    IsHecke (KL n w) (wordUS d w l) ∧ ∃ A B : UL n w → ℂ, IsHecke (KL n w) A ∧ IsHecke (KL n w) B ∧
      (wordLS d a ha w l).s w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A ∧
      (wordLS d a ha w l).t w = ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B ∧
      mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) A) (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) B) =
        ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l) := by
  have hG' := hG
  obtain ⟨hw, hT, hS₀, hBad, hμ⟩ := hG
  have hU : UL n w = ⊤ := if_pos hw
  set C := ctMu (Nat.add_sub_cancel' ha) w (d.μ w) with hC
  have conv : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → IsHecke (KL n w) (lconv f g) :=
    fun hf hg => GlobalTheory.CompanionTheory.UnitaryWord.isHecke_lconv GlobalTheory.CompanionTheory.LocHecke.locAlg (GlobalTheory.CompanionTheory.MatchPowers.isLevel_KL n w) hf hg
  have mul : ∀ {f g : UL n w → ℂ}, IsHecke (KL n w) f → IsHecke (KL n w) g → C (lconv f g) = mconv (C f) (C g) :=
    fun hf hg => hCt E n a ha w hw (d.μ w) hμ _ _ hf hg
  have star : ∀ {f : UL n w → ℂ}, IsHecke (KL n w) f → lfStar (C f) = C (lstar f) :=
    fun hf => (hSt E n a ha w hw (d.μ w) hN _ hf).symm
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have hunit : C (lone (KL n w)) = PositivityTheory.Rg.BcB.F.idem (K2 a (n - a) w) := GlobalTheory.CompanionTheory.MatchUnit.ctMu_lone _ hU _ hμ
  have hlev : d.lev a w = K2 a (n - a) w := by
    unfold LocData.lev
    rw [if_neg hT, if_neg (by simp [hS₀, hBad])]
  have hlev₂ : d.lev₂ a w = K2 a (n - a) w := by
    unfold LocData.lev₂
    rw [if_neg (by simp [hS₀, hBad])]
  have hes : (d.eL a).s w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev a w) = _
    rw [hlev]
  have het : (d.eL a).t w = C (lone (KL n w)) := by
    rw [hunit]
    show PositivityTheory.Rg.BcB.F.idem (d.lev₂ a w) = _
    rw [hlev₂]
  have hstar1 : lfStar (C (lone (KL n w))) = C (lone (KL n w)) := by
    rw [hunit, PositivityTheory.Rg.BcB.F.LocComm.lfStar_idem]
  have hH : ∀ x, IsHecke (KL n w) (letU d w x) := by
    rintro ⟨k, intersection_update_fsHerm_neg_one, st⟩
    have hTk := isHecke_hU d hd hU k
    cases st
    · exact hTk
    · exact isHecke_lstar hTk
  have hck : ∀ k, d.hc a ha w k = C (d.hU w k) := fun k => hc_eq d a ha hμ k
  have hl0 : ∀ k st, (letL d a ha w (k, false, st)).s w = C (letU d w (k, false, st)) ∧
      (letL d a ha w (k, false, st)).t w = C (lone (KL n w)) := by
    intro k st
    have e : (d.hL a ha w k false).s w = d.hc a ha w k := by simp [LocData.hL]
    cases st
    · exact ⟨by simpa [letL, letU] using e.trans (hck k), het⟩
    · refine ⟨?_, ?_⟩
      · show lfStar ((d.hL a ha w k false).s w) = C (lstar (d.hU w k))
        rw [e, hck, star (isHecke_hU d hd hU k)]
      · show lfStar ((d.eL a).t w) = _
        rw [het, hstar1]
  have hl1 : ∀ k st, (letL d a ha w (k, true, st)).s w = C (lone (KL n w)) ∧
      (letL d a ha w (k, true, st)).t w = C (letU d w (k, true, st)) := by
    intro k st
    have e : (d.hL a ha w k true).t w = d.hc a ha w k := by simp [LocData.hL]
    cases st
    · exact ⟨hes, by simpa [letL, letU] using e.trans (hck k)⟩
    · refine ⟨?_, ?_⟩
      · show lfStar ((d.eL a).s w) = _
        rw [hes, hstar1]
      · show lfStar ((d.hL a ha w k true).t w) = C (lstar (d.hU w k))
        rw [e, hck, star (isHecke_hU d hd hU k)]
  induction l with
  | nil =>
    refine ⟨?_, lone (KL n w), lone (KL n w), hone, hone, hes, het, ?_⟩
    · show IsHecke (KL n w) ((KL n w : Set (UL n w)).indicator 1)
      rw [GlobalTheory.CompanionTheory.UnitaryWord.lone_KL] at hone
      exact hone
    · rw [← mul hone hone, lconv_lone_left hone, GlobalTheory.CompanionTheory.UnitaryWord.lone_KL]
      rfl
  | cons x l ih =>
    obtain ⟨hW, A, B, hA, hB, hs, ht, hm⟩ := ih
    obtain ⟨k, intersection_update_fsHerm_neg_one, st⟩ := x
    have hg := hH (k, intersection_update_fsHerm_neg_one, st)
    have hWc : wordUS d w ((k, intersection_update_fsHerm_neg_one, st) :: l) = lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) (wordUS d w l) := rfl
    have hLc : wordLS d a ha w ((k, intersection_update_fsHerm_neg_one, st) :: l) = (letL d a ha w (k, intersection_update_fsHerm_neg_one, st)).mul (wordLS d a ha w l) := rfl
    have key : mconv (C (lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) A)) (C B) = C (lconv (letU d w (k, intersection_update_fsHerm_neg_one, st)) (wordUS d w l)) := by
      rw [← mul (conv hg hA) hB, lconv_assoc hE hg hA hB, mul hg (conv hA hB), mul hA hB, hm, ← mul hg hW]
    refine ⟨hWc ▸ conv hg hW, ?_⟩
    rw [hWc, hLc]
    cases intersection_update_fsHerm_neg_one with
    | false =>
      obtain ⟨e₁, e₂⟩ := hl0 k st
      refine ⟨lconv (letU d w (k, false, st)) A, B, conv hg hA, hB, ?_, ?_, key⟩
      · show mconv ((letL d a ha w (k, false, st)).s w) ((wordLS d a ha w l).s w) = _
        rw [e₁, hs, ← mul hg hA]
      · show mconv ((letL d a ha w (k, false, st)).t w) ((wordLS d a ha w l).t w) = _
        rw [e₂, ht, ← mul hone hB, lconv_lone_left hB]
    | true =>
      obtain ⟨e₁, e₂⟩ := hl1 k st
      refine ⟨A, lconv (letU d w (k, true, st)) B, hA, conv hg hB, ?_, ?_, ?_⟩
      · show mconv ((letL d a ha w (k, true, st)).s w) ((wordLS d a ha w l).s w) = _
        rw [e₁, hs, ← mul hone hA, lconv_lone_left hA]
      · show mconv ((letL d a ha w (k, true, st)).t w) ((wordLS d a ha w l).t w) = _
        rw [e₂, ht, ← mul hg hB]
      · rw [← mul hA (conv hg hB), ← lconv_assoc hE hA hg hB, mul (conv hA hg) hB, mul hA hg,
          hSp E a (n - a) w (C A) (C (letU d w (k, true, st))) (isHecke_ctMu _ hU _ hμ hA) (isHecke_ctMu _ hU _ hμ hg),
          ← mul hg hA]
        exact key

theorem matchLMWordSOf : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := by
  intro hS hCt hSt hSp _ E _ _ _ hE n d hd a ha w hG hN l
  have hP : w ∉ d.P := by simp [LocData.P, hG.2.1, hG.2.2.1]
  have htr : (wordLS d a ha w l).tr d.P d.one w = (wordLS d a ha w l).s w := if_neg hP
  obtain ⟨hW, A, B, -, -, hs, ht, hm⟩ := word_ct d a ha hCt hSt hSp hE hd hG hN l
  rw [htr, hs, ht, hm]
  have hμ := hG.2.2.2.2
  have hw := hG.1
  have h1 := hS E n a ha w hw (d.μ w) hμ _ hW 1 le_rfl
  have hone : IsHecke (KL n w) (lone (KL n w)) := GlobalTheory.CompanionTheory.MatchUnit.isHecke_lone_KL hE
  have e1 : lpow (KL n w) (wordUS d w l) 1 = wordUS d w l := lconv_lone_right hW
  have e2 : mconv (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l))
      (ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (lone (KL n w))) =
      ctMu (Nat.add_sub_cancel' ha) w (d.μ w) (wordUS d w l) := by
    rw [← hCt E n a ha w hw (d.μ w) hμ _ _ hW hone, lconv_lone_right hW]
  rw [e1] at h1
  exact e2 ▸ h1

end GlobalTheory.CompanionTheory.MatchWordS

end

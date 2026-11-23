import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExplicitParameters
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

noncomputable section

namespace GlobalTheory.EX.OB

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

set_option maxHeartbeats 1000000 in

theorem exists_sizeData_over : ∀ (eps cD ch : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (Lv : LevCh P) (D : D7), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → Lv.GamP = GamS C s P.R → Over D P Lv → RecOK s C cD D → HostArith D.host ∧ (∃ L : SizeData₂ D, L.sc = s ∧ WtEq L a b ∧ Val C cD ch L) ∧ D.R = P.R ∧ D.host.TT.image Formalism.HC.Frame.A.val = P.H.TT.image Formalism.HC.Frame.A.val ∧ D.host.T2 = P.H.T2 ∧ D.host.q = P.H.q ∧ D.host.d = P.H.d ∧ D.host.g = P.H.g ∧ D.host.pde = P.H.pde ∧ D.host.pde' = P.H.pde' ∧ P.H.levelPrimes ⊆ D.host.levelPrimes ∧ D.host.u0.val = P.H.u0.val ∧ (∀ l, (G.hP D l).val = (hPH P.H l).val) ∧ ∃ eW : D.what₂.Word ≃ P.Word, ∀ u l, wordBits D u l = if h : l < P.R.k - 2 then c (eW u) ⟨l, h⟩ else false := by
  intro eps cD ch C h0 h1 hC hcD hch
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC hcD hch
  refine ⟨x0, ?_⟩
  intro s P q1 a b c Lv D hs hx hP hG hO hR
  obtain ⟨sp, hT, hY, hA, hV, hz, X, hB, rfl⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ Lv.host.levelPrimes, Lv.host.cls p = .splitK := (Pre.ofCh P Lv sp hT hY hA hV hz).level_split
  refine ⟨⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Finset.subset_union_left, rfl, fun l => rfl, Equiv.refl _, ?_⟩
  · obtain ⟨L, e1, e2, e3, e4⟩ := hx0 s D (fun t => a t.1) (fun t => b t.1) hs hx hP.rank hP.val (hP.hc P.u₀) hP.dlog hR.del hP.ct2
      hP.card hR.etaF (fun u => by
        have e : (D.mem u).A.GamP = Lv.GamP := Cc.A_GamP u
        rw [e, hG, GamS, Real.log_exp]; rfl)
      (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top P.u₀ τ t h ht) hR.untw
    refine ⟨L, e1, ?_, e4⟩
    intro t t' htt
    have : t.1 = t' := Formalism.HC.Frame.A.val_injective _ htt
    rw [e2, e3]
    subst this
    exact ⟨rfl, rfl⟩
  · intro u l
    unfold wordBits
    by_cases h : l < P.R.k - 2
    · have h' : l < D.R.k - 2 := h
      rw [dif_pos h', dif_pos h]
      have τ : Tau P.R := tauPl D (false, 0)
      have a1 := D.s.u_letter u τ l h'
      have a2 := hP.code u τ l h
      have a3 := a1.symm.trans a2
      have hpos := D.s.Del_pos
      rw [← hR.del] at a3
      show D.s.letter u ⟨l, h'⟩ = c u ⟨l, h⟩
      have a4 : (if D.s.letter u ⟨l, h'⟩ = true then D.s.Del else 0) = (if c u ⟨l, h⟩ = true then D.s.Del else 0) :=
        sub_right_injective a3
      revert a4
      cases D.s.letter u ⟨l, h'⟩ <;> cases c u ⟨l, h⟩ <;> simp [hpos.ne', hpos.ne]
    · have h' : ¬ l < D.R.k - 2 := h
      rw [dif_neg h', dif_neg h]

end GlobalTheory.EX.OB

end

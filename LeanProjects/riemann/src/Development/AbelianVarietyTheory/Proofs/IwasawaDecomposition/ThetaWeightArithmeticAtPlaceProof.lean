import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.InfinityTypes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.DivisionValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes Formalism.L2.NTheta

namespace GlobalTheory.PairWeightArith

lemma toNat_floor_cast {x : ℚ} (hz : ∃ z : ℤ, x = z) (h0 : 0 ≤ x) : ((⌊x⌋.toNat : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := hz
  have hz : 0 ≤ z := by exact_mod_cast h0
  rw [Int.floor_intCast]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

lemma lamAt_tail {R : Ranks} (h : HCParam R) (n : ℕ) (c : Fin R.m) (hn : n + 1 = R.k + c) :
    lamAt h n = -h.b c := by
  have hk := R.m_add_three_le_k
  have hc := c.2
  unfold lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr 2
  exact Fin.ext (by simp only; omega)

lemma lamAt_anti {R : Ranks} (h : HCParam R) {a b : ℕ} (hab : a ≤ b) (hb : b < R.r) :
    lamAt h b + b ≤ lamAt h a + a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have := lamAt_add_add_le h d a hb
  push_cast
  linarith

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

lemma sig_eq : pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1) := by
  have h := D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D τ)
  refine ⟨?_, ?_⟩
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = _
    rw [h]; simp [Ranks.sigW]
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).2 = _
    rw [h]; rfl

lemma pq_eq : pS D i τ + qS D i τ = D.R.r := by
  obtain ⟨h1, h2⟩ := sig_eq D i τ
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  rw [h1, h2]; unfold Ranks.r; omega

lemma t_half : ∃ s : ℕ, (D.R.t : ℚ) = 2 * s + 1 := by
  obtain ⟨s, hs⟩ := D.R.t_odd
  exact ⟨s, by exact_mod_cast hs⟩

lemma aPlusQ_int (a : ℕ) : ∃ z : ℤ, aPlusQ D i τ a = z := by
  obtain ⟨s, hs⟩ := t_half D
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) a
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  refine ⟨z + e - (pS D i τ : ℕ) + a - s, ?_⟩
  simp only [aPlusQ, centred, eS, hs, hz, he]
  push_cast; ring

lemma neg_dRowQ_int (c : ℕ) : ∃ z : ℤ, -dRowQ D i τ c = z := by
  obtain ⟨s, hs⟩ := t_half D
  obtain ⟨z, hz⟩ := lamAt_int (D.hc τ) (pS D i τ + c)
  obtain ⟨e, he⟩ := (D.hc τ).e_int i
  refine ⟨-(z + e + c + 1 + s), ?_⟩
  simp only [dRowQ, centred, eS, hs, hz, he]
  push_cast; ring

lemma aPlusQ_anti {a b : ℕ} (hab : a ≤ b) (hb : b < pS D i τ) : aPlusQ D i τ b ≤ aPlusQ D i τ a := by
  have h := pq_eq D i τ
  have := lamAt_anti (D.hc τ) hab (by omega)
  simp only [aPlusQ, centred]
  linarith

lemma dRowQ_anti {a b : ℕ} (hab : a ≤ b) (hb : b < qS D i τ) : dRowQ D i τ b ≤ dRowQ D i τ a := by
  have h := pq_eq D i τ
  have := lamAt_anti (D.hc τ) (Nat.add_le_add_left hab (pS D i τ)) (by omega)
  simp only [dRowQ, centred]
  push_cast at this
  linarith

lemma one_le_aPlusQ {a : ℕ} (ha : a < pS D i τ) : 1 ≤ aPlusQ D i τ a := by
  obtain ⟨n, hn⟩ : ∃ n, pS D i τ = n + 1 := ⟨pS D i τ - 1, by omega⟩
  refine le_trans ?_ (aPlusQ_anti D i τ (show a ≤ n by omega) (by omega))
  have h1 := lamAt_tail (D.hc τ) n i (by rw [← hn]; exact (sig_eq D i τ).1)
  have g := (D.hc τ).gap_be i
  have hn' : (pS D i τ : ℚ) = n + 1 := by exact_mod_cast hn
  simp only [aPlusQ, centred, eS, h1, hn']
  linarith

lemma one_le_neg_dRowQ {c : ℕ} (hc : c < qS D i τ) : 1 ≤ -dRowQ D i τ c := by
  obtain ⟨hp, hq⟩ := sig_eq D i τ
  have h0 := dRowQ_anti D i τ (Nat.zero_le c) hc
  have hi : (i : ℕ) + 1 < D.R.m := by omega
  have h1 := lamAt_tail (D.hc τ) (pS D i τ + 0) ⟨i + 1, hi⟩ (by simp only; omega)
  have g := (D.hc τ).gap_eb i hi
  have : dRowQ D i τ 0 ≤ -1 := by
    simp only [dRowQ, centred, eS, h1]
    push_cast
    linarith
  linarith

lemma cast_aPlus {a : ℕ} (ha : a < pS D i τ) : (aP D i τ a : ℚ) = aPlusQ D i τ a := by
  unfold aP aPl
  rw [if_pos ha]
  exact toNat_floor_cast (aPlusQ_int D i τ a) (le_trans zero_le_one (one_le_aPlusQ D i τ ha))

lemma aM_cast {c : ℕ} (hc : c < qS D i τ) : (aM D i τ (qS D i τ - 1 - c) : ℚ) = -dRowQ D i τ c := by
  unfold aM aMi
  have e1 : qS D i τ - (qS D i τ - 1 - c) = c + 1 := by omega
  rw [if_pos (by omega), e1, show pS D i τ + (c + 1) - 1 = pS D i τ + c by omega]
  have e2 : -((D.hc τ).e i + lamAt (D.hc τ) (pS D i τ + c) + ((c + 1 : ℕ) : ℚ) + ((D.R.t : ℚ) - 1) / 2)
      = -dRowQ D i τ c := by
    simp only [dRowQ, centred, eS]; push_cast; ring
  rw [e2]
  exact toNat_floor_cast (neg_dRowQ_int D i τ c) (le_trans zero_le_one (one_le_neg_dRowQ D i τ hc))

lemma aM_cast' {a : ℕ} (ha : a < qS D i τ) : (aM D i τ a : ℚ) = -dRowQ D i τ (qS D i τ - 1 - a) := by
  rw [← aM_cast D i τ (by omega)]
  congr 2
  omega

lemma lam_eq {w : IndefiniteWeightData.WeightData} (hw : IsDataOf D i τ w) {a : ℕ} (ha : a < D.R.r) :
    (w.lam (a + 1) : ℚ) = lamAt (D.hc τ) a := by
  obtain ⟨hk, -, -, -, -, hv, hb⟩ := hw
  have hk3 := D.R.m_add_three_le_k
  unfold Ranks.r at ha
  unfold IndefiniteWeightData.WeightData.lam
  rw [hk]
  by_cases h : a < D.R.k - 1
  · rw [if_pos (by omega)]
    unfold lamAt
    rw [dif_pos h]
    exact hv ⟨a, h⟩
  · rw [if_neg (by omega), lamAt_tail (D.hc τ) a ⟨a + 1 - D.R.k, by omega⟩ (by simp only; omega),
      ← hb, Int.cast_neg]
    congr 3
    simp only; omega

lemma lamPrime_eq (w : IndefiniteWeightData.WeightData) (hw : IsDataOf D i τ w) (a : ℕ) (ha : a < D.R.r + D.R.t) :
    w.lamPrime (a + 1) = (thetaWt D i τ a : ℚ) + dShift D i τ := by
  obtain ⟨hp, hq⟩ := sig_eq D i τ
  have hr := pq_eq D i τ
  have hl := fun a ha => lam_eq D i τ (a := a) hw ha
  obtain ⟨hk, hm, ht, hj, he, hv, hb⟩ := hw
  have hk3 := D.R.m_add_three_le_k
  have wp : w.p = pS D i τ := by unfold IndefiniteWeightData.WeightData.p; omega
  have wq : w.q = qS D i τ := by unfold IndefiniteWeightData.WeightData.q; omega
  have wn : w.nV = pS D i τ + qS D i τ + D.R.t := by
    unfold IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r; unfold Ranks.r at hr; omega
  unfold IndefiniteWeightData.WeightData.lamPrime
  congr 1
  · unfold IndefiniteWeightData.WeightData.thetaWt thetaWt
    rw [wp, wq, ht]
    by_cases h1 : a < pS D i τ
    · rw [if_pos (by omega), if_pos h1, Int.cast_natCast, cast_aPlus D i τ h1]
      unfold IndefiniteWeightData.WeightData.aPlus
      rw [hl a (by omega), wn, wp, wq, he]
      simp only [aPlusQ, centred]
      push_cast; ring
    · rw [if_neg (by omega), if_neg h1]
      by_cases h2 : a < pS D i τ + D.R.t
      · rw [if_pos (by omega), if_pos h2]; simp
      · rw [if_neg (by omega), if_neg h2]
        obtain ⟨c, rfl⟩ : ∃ c, a = pS D i τ + D.R.t + c := ⟨a - (pS D i τ + D.R.t), by omega⟩
        have hc : c < qS D i τ := by omega
        rw [Nat.add_sub_cancel_left, Int.cast_neg, Int.cast_natCast, aM_cast D i τ hc]
        unfold IndefiniteWeightData.WeightData.aMinus
        have e1 : w.q + 1 - (qS D i τ + 1 - (pS D i τ + D.R.t + c + 1 - pS D i τ - D.R.t)) = c + 1 := by
          omega
        have hi : (i : ℕ) + c + 1 < D.R.m := by omega
        have e2 : (w.b (w.j + (c + 1)) : ℚ) = (D.hc τ).b ⟨i + c + 1, hi⟩ := by
          rw [← hb]; congr 2; simp only; omega
        rw [e1, e2, he, ht]
        simp only [dRowQ, centred]
        rw [lamAt_tail (D.hc τ) (pS D i τ + c) ⟨i + c + 1, hi⟩ (by simp only; omega)]
        push_cast; ring
  · unfold IndefiniteWeightData.WeightData.dTau dShift
    rw [wp, wq, he]

theorem arithAt : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ArithAt D i τ := by
  intro D i τ
  have hr := pq_eq D i τ
  have hV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hr' : (D.R.r : ℚ) = (pS D i τ : ℚ) + (qS D i τ : ℚ) := by exact_mod_cast hr.symm
  have ho : Odd (pS D i τ + qS D i τ) := hr ▸ odd_r D.R
  have hL := GlobalTheory.ForcedWeights.lamLForced D ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 τ
  refine ⟨sig_eq D i τ, ⟨hr, hV⟩, fun a ha => cast_aPlus D i τ ha, fun c hc => aM_cast D i τ hc,
    fun a b hab hb => ?_, fun a b hab hb => ?_, fun a ha => ?_, fun a ha => ?_, fun a => ?_, fun c => ?_, ?_,
    lamPrime_eq D i τ, hL, fun a => ?_⟩
  · rw [← Nat.cast_le (α := ℚ), cast_aPlus D i τ hb, cast_aPlus D i τ (by omega)]
    exact aPlusQ_anti D i τ hab hb
  · rw [← Nat.cast_le (α := ℚ), aM_cast' D i τ hb, aM_cast' D i τ (by omega), neg_le_neg_iff]
    exact dRowQ_anti D i τ (by omega) (by omega)
  · rw [← Nat.cast_le (α := ℚ), cast_aPlus D i τ ha, Nat.cast_one]
    exact one_le_aPlusQ D i τ ha
  · rw [← Nat.cast_le (α := ℚ), aM_cast' D i τ ha, Nat.cast_one]
    exact one_le_neg_dRowQ D i τ (by omega)
  · rw [kapW_cast _ _ _ ho, cast_aPlus D i τ a.2]
    simp only [kapQ, Sum.elim_inl, aPlusQ, centred, hr']; ring
  · rw [kapW_cast _ _ _ ho, aM_cast D i τ c.2]
    simp only [kapQ, Sum.elim_inr, dRowQ, centred, hr']; ring
  · obtain ⟨s, hs⟩ := ho
    have hs' : (qS D i τ : ℚ) = 2 * s + 1 - pS D i τ := by
      have : (pS D i τ : ℚ) + qS D i τ = 2 * s + 1 := by exact_mod_cast hs
      linarith
    obtain ⟨e, he⟩ := (D.hc τ).e_int i
    refine ⟨(pS D i τ : ℕ) - s - 1 - e, ?_⟩
    simp only [dShift, eS, he, hs']
    push_cast; ring
  · obtain ⟨_, w, hk, hm, ht, hj, he, hv, hb, hw⟩ := hL
    rw [hw a]
    exact lamPrime_eq D i τ w ⟨hk, hm, ht, hj, he, hv, hb⟩ a (hV ▸ a.2)

end GlobalTheory.PairWeightArith

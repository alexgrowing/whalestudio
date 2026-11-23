import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.ThickFrames.topsBase

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.TopsOfHost

theorem topsChoice_of
    (hnum : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ e L₂ : ℕ, s.x ^ Formalism.MainNotions.G.hG s / 2 ≤ ((2 ^ e : ℕ) : ℝ) → ((2 ^ e : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → ∀ bs : ZMod (2 ^ e) → ZMod (2 ^ e) → ZMod (2 ^ e), (∀ h t, ∃ i : ℕ, bs h t + i • h = t) → (∀ h t, bs h (t + h) = bs h t) → ∀ (PP : Finset ℕ) (hp : ℕ → ZMod (2 ^ e)) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, s.x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) → ∃ TT : Finset (ZMod (2 ^ e)), s.delta1 * ((2 ^ e : ℕ) : ℝ) / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * s.delta1 * ((2 ^ e : ℕ) : ℝ) ∧ ∑ p ∈ PP, ω p * (({t : ZMod (2 ^ e) | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * ((2 ^ e : ℕ) : ℝ) * ∑ p ∈ PP, ω p) : TopsChoice := by
  intro eps Co he he'
  obtain ⟨Cb, x0, hCb, h⟩ := UpperTheory.BernoulliSumsFrobeniusOrbits.topsBase eps (max Co 2) he he' (le_trans one_le_two (le_max_right _ _))
  refine ⟨Cb, x0, hCb, fun s R H hs hx hR hJC ho hsb => ?_⟩
  subst hs
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hJ : 1 ≤ s.J := s.one_le_J
  have hCo : Co ≤ max Co 2 := le_max_left _ _
  have hpw : 0 < s.x ^ (2 + 8 * s.eps) := Real.rpow_pos_of_pos hx0 _
  have hn1 : s.x ^ (2 + 8 * s.eps) / 2 ≤ (R.n : ℝ) := by linarith [hR.n_lo]
  have hn2 : (R.n : ℝ) ≤ max Co 2 * s.x ^ (2 + 8 * s.eps) :=
    hR.n_up.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpw.le)
  have ho' : (R.toFrame.o : ℝ) ≤ max Co 2 := ho.trans hCo
  have hp : ∀ p : ℕ, p.Prime → H.cls p = PrimeClass.inertClass → s.x ^ (s.eps / (5 * max Co 2)) < p := by
    intro p hp hc
    obtain ⟨h2, -, -, h5, -⟩ := (primeClass_eq_inert_iff H.toHostRaw).1 hc
    have h2' : p ≠ 2 := by
      rintro rfl
      exact h2 H.two_mem_small
    have h6 : ⌊s.x ^ (s.ez / 5)⌋₊ < p := by
      by_contra hle
      exact h5 (H.split_small p hp h2' ((not_lt.mp hle).trans hsb))
    have h7 : s.x ^ (s.ez / 5) < p := (Nat.floor_lt (Real.rpow_nonneg hx0.le _)).1 h6
    refine lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le ?_) h7
    unfold Scale.ez
    rw [div_div]
    exact div_le_div_of_nonneg_left s.eps_pos.le (by linarith) (by linarith)
  obtain ⟨TT, t1, t2, t3, t4⟩ := h (baseOf s 0 0 H) (hPH H) rfl hx hn1 hn2 ho' hR.2.2.1.2 hp
  exact ⟨TT, t1, t2, t4, t3⟩

end GlobalTheory.EX.TopsOfHost

end

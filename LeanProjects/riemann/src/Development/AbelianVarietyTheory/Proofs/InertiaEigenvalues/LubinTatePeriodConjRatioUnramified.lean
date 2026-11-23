import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOfFrobeniusIterateFixedFilZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

set_option maxHeartbeats 1000000 in

theorem lt_period_conj_ratio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (s : ℕ), 0 < s → ∀ (x : P.R.B), IsUnit x → P.φB^[s] x = (l : P.R.B) * x → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → ∀ g : GQ l, ∃ a : ↥(MaximalUnramifiedExtension l), fr l s a = a ∧ P.actQ g x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B a * x := by
  intro l _ P AI T s hs x hx hφ h1 h2 hj g
  obtain ⟨-, -, hsh, hinv, -, -, -, htz, tadd, t0, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  have iter_mul : ∀ (m : ℕ) (a b : P.R.B), P.φB^[m] (a * b) = P.φB^[m] a * P.φB^[m] b := by
    intro m a b
    induction m generalizing a b with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply', ih, map_mul]
  have iter_one : ∀ m : ℕ, P.φB^[m] (1 : P.R.B) = 1 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_one]
  have iter_act : ∀ (m : ℕ) (b : P.R.B), P.φB^[m] (P.actQ g b) = P.actQ g (P.φB^[m] b) := by
    intro m b
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, phiB_actQ]
  have ev_mul : ∀ (m : ℕ) (a b : P.R.B), ev P m (a * b) = ev P m a * ev P m b := by
    intro m a b
    rw [← evHom_apply, map_mul, evHom_apply, evHom_apply]
  obtain ⟨w, hw⟩ : ∃ w : P.R.B, x * w = 1 := ⟨_, hx.mul_val_inv⟩
  set y := P.actQ g x * w with hy
  have hyx : y * x = P.actQ g x := by rw [hy, mul_assoc, mul_comm w x, hw, mul_one]

  have hfix : P.φB^[s] y = y := by
    have e1 : P.φB^[s] x * P.φB^[s] w = 1 := by rw [← iter_mul, hw, iter_one]
    rw [hφ] at e1
    rw [hy, iter_mul, iter_act, hφ, map_mul, map_natCast]
    calc (l : P.R.B) * P.actQ g x * P.φB^[s] w = P.actQ g x * (((l : P.R.B) * x * P.φB^[s] w) * w) := by
          linear_combination (-(l : P.R.B) * P.actQ g x * P.φB^[s] w) * hw
      _ = P.actQ g x * w := by rw [e1, one_mul]

  have key : ∀ (k : ℤ) (e u v z : P.R.BdR), e = tz P k * u → u * v = 1 → u ∈ Fil P 0 → v ∈ Fil P 0 →
      z * e = P.actQdR g e → z ∈ Fil P 0 := by
    intro k e u v z he huv hu hv hz
    have hk : tz P k * tz P (-k) = 1 := by rw [← tadd, add_neg_cancel, t0]
    have hz' : z * e = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * tz P k * P.actQdR g u := by
      rw [hz, he, map_mul, htz]
    have hzz : z = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR g u * v := by
      linear_combination (-z + algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ k : ℚ_[l]ˣ) : ℚ_[l]) * P.actQdR g u * v) * hk
        - z * tz P k * tz P (-k) * huv - tz P (-k) * v * z * he + tz P (-k) * v * hz'
    rw [hzz]
    exact Fil_mul_right (Fil_mul_left (q_mem_Fil P _) (Fil_act g hu)) hv
  have hev : ∀ j, ev P j y * ev P j x = P.actQdR g (ev P j x) := by
    intro j
    rw [← ev_mul, hyx, ev_act]
  have hfil : ∀ j < s, ev P j y ∈ Fil P 0 := by
    intro j hjs
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · have hu0 : tz P (-1) * P.ιB x ∈ Fil P 0 := by
        have := (hsh 1 (-1) (P.ιB x)).1 h1
        rwa [show (1 : ℤ) + -1 = 0 by norm_num] at this
      have hu1 : tz P (-1) * P.ιB x ∉ Fil P 1 := by
        intro h
        apply h2
        exact (hsh 2 (-1) (P.ιB x)).2 (by rw [show (2 : ℤ) + -1 = 1 by norm_num]; exact h)
      obtain ⟨v, hv, huv⟩ := hinv _ hu0 hu1
      refine key 1 (ev P 0 x) _ v _ ?_ huv hu0 hv (hev 0)
      change P.ιB x = tz P 1 * (tz P (-1) * P.ιB x)
      rw [← mul_assoc, ← tadd, show (1 : ℤ) + -1 = 0 by norm_num, t0, one_mul]
    · obtain ⟨e0, e1⟩ := hj j hpos hjs
      obtain ⟨v, hv, huv⟩ := hinv _ e0 e1
      exact key 0 (ev P j x) (ev P j x) v _ (by rw [t0, one_mul]) huv e0 hv (hev j)
  obtain ⟨a, ha, hya⟩ := GlobalTheory.T.unramified_of_frobeniusIterate_fixed_filZero l P AI T s hs y hfix hfil
  exact ⟨a, ha, by rw [← hyx, hya]⟩

end GlobalTheory.PMon

end

import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField

namespace Formalism.MainNotions.DIV.HookProducts.AdmPerTw

variable {D : D7}

theorem vAdd_dvd_le (w : D.what₂.places.Pl) {n N : ℕ} (hN : N ≠ 0) (hd : n ∣ N) :
    (vAdd (D.plEq w) (n : D.what₂.LL) : ℝ) ≤ ur D w (padicValNat (D.what₂.places.resChar w) N : ℝ) := by
  have hpp := D.what₂.places.resChar_prime w
  have hn : n ≠ 0 := fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  set p := D.what₂.places.resChar w with hp
  set k := padicValNat p n with hk
  obtain ⟨n', hn'⟩ : ∃ n', n' = n / p ^ n.factorization p := ⟨_, rfl⟩
  have hfac : n.factorization p = k := by rw [hk, Nat.factorization_def n hpp]
  have hprod : p ^ k * n' = n := by
    rw [hn', ← hfac]; exact Nat.ordProj_mul_ordCompl_eq_self n _
  have hcop : Nat.Coprime n' p := by
    rw [hn']; exact (Nat.coprime_ordCompl hpp hn).symm
  have hn'0 : n' ≠ 0 := by rintro rfl; simp at hprod; exact hn hprod.symm
  have hv' : vAdd (D.plEq w) ((n' : ℕ) : D.what₂.LL) = 0 := by
    have h := OrbitPlaces.val_coprime w n' hcop
    rw [D.val_eq w _ (Nat.cast_ne_zero.2 hn'0)] at h
    exact_mod_cast h
  have hpk : ((p : ℕ) : D.what₂.LL) ^ k ≠ 0 := pow_ne_zero _ (OrbitPlaces.p_ne w)
  have hv : vAdd (D.plEq w) (n : D.what₂.LL) = (k : ℤ) * (D.what₂.places.ramIdx w : ℤ) := by
    rw [← hprod, Nat.cast_mul, Nat.cast_pow, OrbitPlaces.vAdd_mul w hpk (Nat.cast_ne_zero.2 hn'0), OrbitPlaces.vAdd_pow, hv', add_zero]
  have hkN : k ≤ padicValNat p N := (padicValNat_dvd_iff_le hN).1 (pow_padicValNat_dvd.trans hd)
  rw [hv]
  unfold ur
  push_cast
  have h0 : (0 : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) := Nat.cast_nonneg _
  have h1 : (k : ℝ) ≤ (padicValNat p N : ℝ) := by exact_mod_cast hkN
  nlinarith

theorem card_stabilizer_dvd₂ (hD : DGamDef D) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (c : (T.fm u μ).clsP) :
    Nat.card ((T.fm u μ).stabilizer₂ c) ∣ (D.mem u).C.DGam := by
  rw [← DGamDef.one hD u u μ]
  refine dvd_trans ?_ ((D.chTw u μ).dvd_DGam D.R.m le_rfl ((T.fm u μ).til c))
  rw [Nat.card_congr (MonoidHom.ofInjective ((T.fm u μ).stabMap_inj c)).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem twisted_period_of_class_decomposition {Dx : DivX D} {T : TwForms D}
    (h : ∀ u μ, μ ≠ D.what₂.mu0 → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) : Formalism.MainNotions.WeightDegreeSizes.TwistedPeriodIntegral D Dx T := by
  intro hD u μ hμ x hx F hF _
  obtain ⟨pc, hs, hi⟩ := h u μ hμ
  choose y hy hv using hi x hx F hF
  refine ⟨∑ c, ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c, ?_, fun w hw => ?_⟩
  · rw [hs, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_inv₀, map_natCast, hy c]
  · refine Finset.sum_induction _ (fun t => t = 0 ∨ -ur D w (Formalism.MainNotions.WeilJacquetShalikaLaw.vDG D u w) ≤ (vAdd (D.plEq w) t : ℝ))
      (fun a b ha hb => Formalism.MainNotions.WeightDegreeSizes.pair_add_ge D w ha hb) (Or.inl rfl) fun c _ => ?_
    rcases hv c w hw with h0 | h0
    · left; rw [h0, mul_zero]
    by_cases hy0 : y c = 0
    · left; rw [hy0, mul_zero]
    right
    have hn0 : ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [OrbitPlaces.vAdd_mul w (inv_ne_zero hn0) hy0, OrbitPlaces.vAdd_inv w hn0]
    have hb := vAdd_dvd_le (D := D) w (D.mem u).C.DGam_pos.ne' (card_stabilizer_dvd₂ hD T u μ c)
    have h0' : (0 : ℝ) ≤ (vAdd (D.plEq w) (y c) : ℝ) := by exact_mod_cast h0
    unfold Formalism.MainNotions.WeilJacquetShalikaLaw.vDG
    push_cast
    linarith

end Formalism.MainNotions.DIV.HookProducts.AdmPerTw

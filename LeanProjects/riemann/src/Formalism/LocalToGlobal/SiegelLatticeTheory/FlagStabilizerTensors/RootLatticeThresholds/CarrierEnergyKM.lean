import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPlace

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.Pf.Carrier

namespace Formalism.L2.SG.Pf.Carrier.EnergyKM

theorem gam_eq (k r : ℕ) (κ δ : ℝ) : Formalism.FourierDecayAlt.D.GamLev k r κ δ 0 =
    (∏ a : Fin r, κ ^ (-((4 * (r - a.val) * (2 * (r - a.val) + k) : ℕ) : ℤ))) / δ ^ (r + 1) := by
  have hI : ∀ f : ℕ → ℝ, ∏ l ∈ Finset.Ioc 0 r, f l = ∏ i : Fin r, f (i.val + 1) := by
    intro f
    have hset : Finset.Ioc 0 r = Finset.Ico (0 + 1) (r + 1) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [Fin.prod_univ_eq_prod_range (fun i => f (i + 1)) r, Finset.range_eq_Ico,
      Finset.prod_Ico_add' f 0 r 1, hset]
  unfold Formalism.FourierDecayAlt.D.GamLev
  rw [Finset.prod_div_distrib, Finset.prod_const, Nat.card_Ioc, Nat.sub_zero,
    Finset.prod_Ioc_succ_top (Nat.zero_le r), hI]
  congr 1
  simp only [Nat.cast_add, Nat.cast_one, sub_self, mul_zero, zero_mul, neg_zero, zpow_zero, mul_one]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  have ha : a.val ≤ r := a.isLt.le
  simp only [Formalism.FourierDecayAlt.C.Mlev]
  push_cast [Nat.cast_sub ha]
  congr 1
  ring

theorem level_constant_mul_gamma (r k : ℕ) (g rd : ℝ) (hg : 0 < g) (hrd : 0 < rd) :
    (2 : ℝ) ^ (r + 1) * (∏ a : Fin r, (((g / (2 * Real.pi)) ^ (2 * (r - a.val))) ^
      (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹) * Formalism.FourierDecayAlt.D.GamLev k r (Formalism.FourierDecayAlt.D.kapG g rd) (Formalism.FourierDecayAlt.D.deG g rd) 0 =
    rd ^ ((r + 1) + ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k)) * g ^ (3 * (r + 1)) := by
  rw [gam_eq]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hper : ∀ a : Fin r, (((g / (2 * Real.pi)) ^ (2 * (r - a.val))) ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)))⁻¹ *
      Formalism.FourierDecayAlt.D.kapG g rd ^ (-((4 * (r - a.val) * (2 * (r - a.val) + k) : ℕ) : ℤ)) =
      rd ^ (4 * (r - a.val) * (2 * (r - a.val) + k)) := by
    intro a
    have hM : 2 * (r - a.val) * (2 * (Formalism.QuantumDeterminants.Mdim k r a - 1)) = 4 * (r - a.val) * (2 * (r - a.val) + k) := by
      unfold Formalism.QuantumDeterminants.Mdim
      rw [Nat.add_sub_cancel]
      ring
    rw [← pow_mul, hM, zpow_neg, zpow_natCast, ← mul_inv, ← mul_pow]
    unfold Formalism.FourierDecayAlt.D.kapG
    rw [show g / (2 * Real.pi) * (2 * Real.pi / (g * rd)) = rd⁻¹ by field_simp, inv_pow, inv_inv]
  rw [mul_div_assoc', mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun a _ => hper a),
    Finset.prod_pow_eq_pow_sum]
  unfold Formalism.FourierDecayAlt.D.deG
  rw [div_pow, div_div_eq_mul_div, pow_add]
  field_simp
  ring

theorem three_dvd (r : ℕ) : 3 ∣ (r + 1) * (8 * r ^ 2 + 10 * r + 3) := by
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, r = 3 * q ∨ r = 3 * q + 1 ∨ r = 3 * q + 2 := ⟨r / 3, by omega⟩
  · subst hq
    exact ⟨(3 * q + 1) * (24 * q ^ 2 + 10 * q + 1), by ring⟩
  · subst hq
    exact ⟨(3 * q + 2) * (2 * q + 1) * (12 * q + 7), by ring⟩
  · subst hq
    exact ⟨(q + 1) * (8 * (3 * q + 2) ^ 2 + 10 * (3 * q + 2) + 3), by ring⟩

theorem sum_closed (r k : ℕ) :
    3 * ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + k) = 4 * r * (r + 1) * (2 * r + 1) + 6 * k * r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

theorem exp_eq (r k : ℕ) (hk : 1 ≤ k) :
    (r + 1) + ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k) =
      2 * r * (r + 1) * (k - 1) + (r + 1) * (8 * r ^ 2 + 10 * r + 3) / 3 := by
  have hs : ∑ a : Fin r, 4 * (r - a.val) * (2 * (r - a.val) + k) =
      ∑ j ∈ Finset.range r, 4 * (j + 1) * (2 * (j + 1) + k) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 4 * (r - i) * (2 * (r - i) + k)) r, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hj' : r - (r - 1 - j) = j + 1 := by omega
    simp only [hj']
  have h3 := sum_closed r k
  obtain ⟨W, hW⟩ := three_dvd r
  rw [hs, hW, Nat.mul_div_cancel_left W (by norm_num : 0 < 3)]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  nlinarith [h3, hW]

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem kMatch_holds (P : Parts X u u') : EnergyPlace.KMatch P := by
  intro hg hrd hr hk hgpos hk1
  have hrdpos : 0 < Formalism.FourierDecayAlt.S6.rd D.host.E := by rw [hrd]; exact EnergyConst.rdE_pos'
  have hgpos' : (0 : ℝ) < P.S.g := by exact_mod_cast hgpos
  have hκ : 0 < Formalism.FourierDecayAlt.D.kapG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) := by
    simp only [Formalism.FourierDecayAlt.D.kapG]; positivity
  have hδ : 0 < Formalism.FourierDecayAlt.D.deG P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) := by
    simp only [Formalism.FourierDecayAlt.D.deG]; positivity
  have hG : P.Gam0 ≠ 0 := by
    rw [Parts.Gam0, gam_eq]
    exact ne_of_gt (div_pos (Finset.prod_pos fun a _ => zpow_pos hκ _) (pow_pos hδ _))
  have key := level_constant_mul_gamma P.S.G.r P.S.G.k P.S.g (Formalism.FourierDecayAlt.S6.rd D.host.E) hgpos' hrdpos
  rw [exp_eq _ _ hk1] at key
  rw [EnergyConst.Kexp, eq_div_iff hG]
  refine key.trans ?_
  rw [hrd, hg, hr, hk]
  rfl

end Formalism.L2.SG.Pf.Carrier.EnergyKM

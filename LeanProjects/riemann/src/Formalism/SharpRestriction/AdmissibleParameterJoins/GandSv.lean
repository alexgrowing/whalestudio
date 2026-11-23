import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSu

noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section Ab

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

theorem cc_ph : PowerSeries.constantCoeff g.ph = 0 := by
  rw [Formalism.MainNotions.GL3Theta.G1.ph.eq_1, map_neg, neg_eq_zero]
  show Formalism.MainNotions.GL3Theta.logMv _ 0 = 0
  rw [Formalism.MainNotions.GL3Theta.logMv.eq_1]
  simp

theorem be_ab (i0 : K0 p →+* ℂ_[p]) (be : MvPowerSeries (Fin 2) (K0 p)) (ep : ℂ_[p]) (hep : ep ≠ 0)
    (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    (n : Fin 2 →₀ ℕ) (hn : coeff n be ≠ 0) : 1 ≤ n 0 ∧ 1 ≤ n 1 := by
  classical
  set c : ℂ_[p] := ep⁻¹ with hc
  set ψ : PowerSeries ℂ_[p] :=
    PowerSeries.subst (PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) g.ex) g.ph with hψ
  have hcX : PowerSeries.constantCoeff (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) = 0 := by simp
  have hE : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) g.ex) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hcX _ hex
  have hψ0 : PowerSeries.coeff 0 ψ = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.constantCoeff_subst_eq_zero hE _ (cc_ph g)
  have key : ∀ z : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff z = 0 →
      g.phAt (g.pt (C c * z)) = PowerSeries.subst z ψ := by
    intro z hz
    have hz' := PowerSeries.HasSubst.of_constantCoeff_zero hz
    rw [hψ, PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hE) hz',
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hcX) hz',
      PowerSeries.subst_mul hz', PowerSeries.subst_C, PowerSeries.subst_X hz']
    rfl
  have h0 : ∀ i : Fin 2, constantCoeff (C c * X i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by intro i; simp
  have hB : map i0 be = PowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ψ -
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ψ -
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ψ := by
    have h := be_at g i0 be ep hex be_tie (cc_pt g hex (h0 0)) (cc_pt g hex (h0 1))
    rw [lg_pt g hex hinv (h0 0), lg_pt g hex hinv (h0 1)] at h
    have e : (![C ep * (C c * X 0), C ep * (C c * X 1)] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]) = X := by
      funext s
      fin_cases s
      · show C ep * (C c * X 0) = X 0
        rw [← mul_assoc, ← map_mul, hc, mul_inv_cancel₀ hep, map_one, one_mul]
      · show C ep * (C c * X 1) = X 1
        rw [← mul_assoc, ← map_mul, hc, mul_inv_cancel₀ hep, map_one, one_mul]
    rw [e, subst_self] at h
    have h' : map i0 be = g.be (g.pt (C c * X 0)) (g.pt (C c * X 1)) := h
    rw [h']
    unfold G1.be G1.add
    rw [lg_pt g hex hinv (h0 0), lg_pt g hex hinv (h0 1), ← mul_add, key _ (by simp), key _ (by simp),
      key _ (by simp)]
  have hco : i0 (coeff n be) = ((n 0 + n 1).choose (n 0) : ℂ_[p]) * PowerSeries.coeff (n 0 + n 1) ψ -
      (if n = Finsupp.single 0 (n 0) then PowerSeries.coeff (n 0) ψ else 0) -
      (if n = Finsupp.single 1 (n 1) then PowerSeries.coeff (n 1) ψ else 0) := by
    rw [← coeff_map, hB, map_sub, map_sub, PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_single,
      PowerSeries.coeff_subst_single]
  by_contra hcon
  apply hn
  apply i0.injective
  rw [map_zero, hco]
  have hcase : n 0 = 0 ∨ n 1 = 0 := by
    by_contra h
    push Not at h
    exact hcon ⟨Nat.one_le_iff_ne_zero.2 h.1, Nat.one_le_iff_ne_zero.2 h.2⟩
  rcases hcase with h | h
  · have e1 : n = Finsupp.single 1 (n 1) := by
      ext i
      fin_cases i
      · simp [h]
      · simp
    rw [if_pos e1, h, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul]
    split_ifs with h2
    · have : n 1 = 0 := by rw [h2]; simp
      rw [this, hψ0]; ring
    · ring
  · have e1 : n = Finsupp.single 0 (n 0) := by
      ext i
      fin_cases i
      · simp
      · simp [h]
    rw [if_pos e1, h, add_zero, Nat.choose_self, Nat.cast_one, one_mul]
    split_ifs with h2
    · have : n 0 = 0 := by rw [h2]; simp
      rw [this, hψ0]; ring
    · ring

end Ab

variable {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}

end Formalism.MainNotions.J

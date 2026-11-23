import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ExpansionAllPlacesOfPlace

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser Aser Aser' AA leadT G1)

section Scale

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

theorem th_vp_ne (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) : vp ≠ 0 := by
  intro hv
  have hpos : p ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero hp.out.one_lt)
  rw [hv, zero_pow hpos] at hvp
  have hp0 : (p : K') ≠ 0 := by
    rw [← map_natCast (algebraMap (K0 p) K')]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact hp0 hvp.symm

theorem th_wt_AA (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) {x y : Fin 2} (hxy : x ≠ y) (d : Fin 2 →₀ ℕ) :
    ∃ r ∈ Rp p K' vp, vp ^ d.degree * MvPowerSeries.coeff d (AA K' p x y - leadT K' p x y) = vp ^ (p + 1) * r := by
  classical
  have hp2 := hp.out.two_le
  rw [map_sub, Formalism.InvariantFactorPaths.G7.leadT_eq, MvPowerSeries.coeff_monomial]
  by_cases hd : d = Finsupp.single x 1 + Finsupp.single y p
  · have hx : d x = (p ^ 2) ^ 0 := by rw [hd]; simp [hxy.symm]
    have hy : d y = p * (p ^ 2) ^ 0 := by rw [hd]; simp [hxy]
    rw [if_pos hd, Formalism.InvariantFactorPaths.G7.coeff_AA_of K' hp2 le_rfl hx hy]
    exact ⟨0, (Rp p K' vp).zero_mem, by simp⟩
  · rw [if_neg hd, sub_zero]
    by_cases h : MvPowerSeries.coeff d (AA K' p x y) = 0
    · exact ⟨0, (Rp p K' vp).zero_mem, by rw [h]; simp⟩
    · obtain ⟨i, j, hij, hx, hy⟩ := Formalism.InvariantFactorPaths.G7.coeff_AA_ne_zero h
      have hj : 1 ≤ j := by
        by_contra hj
        obtain rfl : j = 0 := by omega
        obtain rfl : i = 0 := by omega
        apply hd
        ext z
        rcases Formalism.InvariantFactorPaths.G7.finset_fin_two_eq_cases x y hxy z with rfl | rfl
        · simp [hx, hxy.symm]
        · simp [hy, hxy]
      have h4 : 4 ≤ p ^ 2 := by nlinarith
      obtain ⟨gi, hgi, hi', _⟩ := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.geom_sum_mul_pred h4 i
      obtain ⟨gj, hgj, hj', _⟩ := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.geom_sum_mul_pred h4 j
      have hle : i + j + 1 ≤ gi + p * gj := by nlinarith
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have hdeg : d.degree = (p ^ 2 - 1) * k + (p ^ 2 - 1) * (i + j + 1) + (p + 1) := by
        rw [Formalism.InvariantFactorPaths.G7.degree_fin_two_eq_add_of_ne hxy, hx, hy, hgi, hgj]
        have : (p ^ 2 - 1) * gi + 1 + p * ((p ^ 2 - 1) * gj + 1) = (p ^ 2 - 1) * (gi + p * gj) + (p + 1) := by ring
        rw [this, hk]
        ring
      refine ⟨(p : K') ^ k, (Rp p K' vp).pow_mem (natCast_mem _ p) k, ?_⟩
      rw [Formalism.InvariantFactorPaths.G7.coeff_AA_of K' hp2 hij hx hy, hdeg, pow_add, pow_add, pow_mul, pow_mul, hvp]
      have hp0 := pK'_ne p K'
      field_simp

theorem exists_atPi_G1_eq_C_pow_mul_integral_series (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) {c c' : K'} (hc : c ∈ Rp p K' vp)
    (hc' : c' ∈ Rp p K' vp) :
    ∃ Rr : MvPowerSeries (Fin 2) K', IntR (Rp p K' vp) Rr ∧ MvPowerSeries.constantCoeff Rr = 0 ∧
      atPi vp (G1 p c c') = MvPowerSeries.C (vp ^ (p + 1)) * Rr := by
  have hv : vp ^ (p + 1) ≠ 0 := pow_ne_zero _ (th_vp_ne p K' vp hvp)
  refine ⟨MvPowerSeries.C ((vp ^ (p + 1))⁻¹) * atPi vp (G1 p c c'), fun d => ?_, ?_, ?_⟩
  · obtain ⟨r1, hr1, e1⟩ := th_wt_AA p K' vp hvp (show (0 : Fin 2) ≠ 1 by decide) d
    obtain ⟨r2, hr2, e2⟩ := th_wt_AA p K' vp hvp (show (1 : Fin 2) ≠ 0 by decide) d
    rw [MvPowerSeries.coeff_C_mul]
    have e : MvPowerSeries.coeff d (atPi vp (G1 p c c')) = vp ^ (p + 1) * (c * r1 - c' * r2) := by
      show vp ^ d.degree * MvPowerSeries.coeff d (G1 p c c') = _
      unfold G1
      rw [map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
      linear_combination c * e1 - c' * e2
    rw [e, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]
    exact (Rp p K' vp).sub_mem ((Rp p K' vp).mul_mem hc hr1) ((Rp p K' vp).mul_mem hc' hr2)
  · rw [map_mul]
    have : MvPowerSeries.constantCoeff (atPi vp (G1 p c c')) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show vp ^ (0 : Fin 2 →₀ ℕ).degree * MvPowerSeries.coeff 0 (G1 p c c') = 0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.InvariantFactorPaths.G7.constant_coeff_g_one hp.out.ne_zero, mul_zero]
    rw [this, mul_zero]
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hv, map_one, one_mul]

end Scale

theorem th_subst_scale {κ τ R : Type} [Finite κ] [CommRing R] (vp : R) (s : κ → MvPowerSeries τ R)
    (hs : MvPowerSeries.HasSubst s) (f : MvPowerSeries κ R) :
    MvPowerSeries.subst (fun k => MvPowerSeries.C vp * s k) f = MvPowerSeries.subst s (atPi vp f) := by
  rw [atPi_eq_rescale, MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.smul_X _) hs]
  congr 1
  funext k
  have : ((fun _ : κ => vp) • (MvPowerSeries.X : κ → MvPowerSeries κ R)) k =
      MvPowerSeries.C vp * MvPowerSeries.X k := by
    rw [Pi.smul_apply', MvPowerSeries.smul_eq_C_mul]
  rw [this, ← MvPowerSeries.coe_substAlgHom hs, map_mul, MvPowerSeries.substAlgHom_X]
  congr 1
  exact ((MvPowerSeries.substAlgHom hs).commutes vp).symm

theorem th_map_Gser {p : ℕ} {K K2 : Type} [Field K] [Field K2] (φ : K →+* K2) (c c' : K) :
    MvPowerSeries.map φ (Gser p c c') = Gser p (φ c) (φ c') := by
  unfold Gser
  rw [map_sub, map_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_C]
  unfold Aser Aser'
  congr 2
  · funext n
    change φ (∑ i ∈ Finset.range (n 0 + 1), ∑ j ∈ Finset.range (n 1 + 1),
      if i ≤ j ∧ n 0 = (p ^ 2) ^ i ∧ n 1 = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0) = _
    simp [map_sum, apply_ite, map_inv₀]
  · funext n
    change φ (∑ i ∈ Finset.range (n 1 + 1), ∑ j ∈ Finset.range (n 0 + 1),
      if i ≤ j ∧ n 1 = (p ^ 2) ^ i ∧ n 0 = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0) = _
    simp [map_sum, apply_ite, map_inv₀]

end Formalism.MainNotions.FormalGroupSystem.Pf

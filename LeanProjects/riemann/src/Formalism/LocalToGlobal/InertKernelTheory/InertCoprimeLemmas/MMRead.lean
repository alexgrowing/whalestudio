import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

namespace ParameterChangeLemmas

open IntegralOrthonormalChange

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_inVar_eq_zero {σ : Type*} (i : σ) (f : PowerSeries ℂ_[p]) (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) f hf

theorem integral_subst_single_variable {σ : Type*} (i : σ) (f : PowerSeries ℂ_[p]) (hf : ∀ n, IsIntP (PowerSeries.coeff n f)) :
    IntegralMv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) := by
  intro n
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · exact hf _
  · show ‖(0 : ℂ_[p])‖ ≤ 1
    simp

theorem integral_prod {σ ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ ℂ_[p])
    (hf : ∀ i ∈ s, IntegralMv (f i)) : IntegralMv (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f IntegralMv (fun a b ha hb => IntegralOrthonormalChange.integral_mul ha hb) ?_ hf
  intro n
  show ‖MvPowerSeries.coeff n (1 : MvPowerSeries σ ℂ_[p])‖ ≤ 1
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem subst_single_var {σ τ : Type*} (S : σ → MvPowerSeries τ ℂ_[p]) (hS : MvPowerSeries.HasSubst S)
    (f : PowerSeries ℂ_[p]) (i : σ) :
    MvPowerSeries.subst S (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) =
      PowerSeries.subst (S i) f := by
  have hX : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p])) :=
    (PowerSeries.HasSubst.X i).const
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hX hS, PowerSeries.subst]
  congr 1
  funext _
  exact MvPowerSeries.subst_X hS i

theorem subst_inv {σ : Type*} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries ℂ_[p]) : PowerSeries.subst a f⁻¹ = (PowerSeries.subst a f)⁻¹ := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  by_cases hf : PowerSeries.constantCoeff f = 0
  · have h1 : f⁻¹ = 0 := PowerSeries.inv_eq_zero.mpr hf
    have h2 : MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero ha f hf
    rw [h1, MvPowerSeries.inv_eq_zero.mpr h2, ← PowerSeries.coe_substAlgHom hs, map_zero]
  · have hm : PowerSeries.subst a f * PowerSeries.subst a f⁻¹ = 1 := by
      rw [← PowerSeries.subst_mul hs, PowerSeries.mul_inv_cancel f hf, ← PowerSeries.coe_substAlgHom hs, map_one]
    have hc : MvPowerSeries.constantCoeff (PowerSeries.subst a f) ≠ 0 := by
      intro h0
      have := congrArg MvPowerSeries.constantCoeff hm
      rw [map_mul, h0, zero_mul, map_one] at this
      exact zero_ne_one this
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one hc, mul_comm, hm]

private theorem exists_integral_subst_inverse_of_unit_linear (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0)
    (hI : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) (h1 : ‖PowerSeries.coeff 1 h‖ = 1) :
    ∃ g : PowerSeries ℂ_[p], PowerSeries.constantCoeff g = 0 ∧ (∀ n, ‖PowerSeries.coeff n g‖ ≤ 1) ∧
      ‖PowerSeries.coeff 1 g‖ = 1 ∧ PowerSeries.subst h g = PowerSeries.X := by
  set u := PowerSeries.coeff 1 h with hudef
  have hu0 : u ≠ 0 := by
    intro hu
    rw [hu, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨h', hh'⟩ : PowerSeries.X ∣ h := PowerSeries.X_dvd_iff.mpr h0
  have hcc : PowerSeries.constantCoeff h' = u := by
    rw [hudef, hh', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hpow : ∀ m k, PowerSeries.coeff k (h ^ m) =
      if m ≤ k then PowerSeries.coeff (k - m) (h' ^ m) else 0 := by
    intro m k
    rw [hh', mul_pow, PowerSeries.coeff_X_pow_mul']
  have hlow : ∀ m k, k < m → PowerSeries.coeff k (h ^ m) = 0 := by
    intro m k hk
    rw [hpow, if_neg (by omega)]
  have hdiag : ∀ m, PowerSeries.coeff m (h ^ m) = u ^ m := by
    intro m
    rw [hpow, if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hcc]
  let b : ℕ → ℂ_[p] := Nat.strongRec fun n rec =>
    (u ^ n)⁻¹ * PowerSeries.coeff n
      (PowerSeries.X - ∑ m : Fin n, PowerSeries.C (rec m m.isLt) * h ^ (m : ℕ))
  have hb : ∀ n, b n = (u ^ n)⁻¹ * PowerSeries.coeff n
      (PowerSeries.X - ∑ m ∈ Finset.range n, PowerSeries.C (b m) * h ^ m) := by
    intro n
    rw [← Fin.sum_univ_eq_sum_range (fun m => PowerSeries.C (b m) * h ^ m) n]
    exact Nat.strongRecOn'_beta _ n
  have hcoeffP : ∀ N k, PowerSeries.coeff k (∑ m ∈ Finset.range N, PowerSeries.C (b m) * h ^ m) =
      ∑ m ∈ Finset.range N, b m * PowerSeries.coeff k (h ^ m) := by
    intro N k
    simp only [map_sum, PowerSeries.coeff_C_mul]
  have hA : ∀ N, ∀ k < N, PowerSeries.coeff k
      (PowerSeries.X - ∑ m ∈ Finset.range N, PowerSeries.C (b m) * h ^ m) = 0 := by
    intro N
    induction N with
    | zero => intro k hk; omega
    | succ N ih =>
      intro k hk
      rw [Finset.sum_range_succ, ← sub_sub, map_sub]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · rw [ih k hk, PowerSeries.coeff_C_mul, hlow N k hk, mul_zero, sub_zero]
      · subst hk
        rw [PowerSeries.coeff_C_mul, hdiag, hb k, mul_comm ((u ^ k)⁻¹) _, mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero k hu0), mul_one, sub_self]
  have hb0 : b 0 = 0 := by
    rw [hb 0]
    simp
  have hb1 : b 1 = u⁻¹ := by
    rw [hb 1]
    simp [hb0]
  have hH : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hhI : Formalism.L2.Th1.C.IntPS (IntegralOrthonormalChange.intRing p) h := fun n => hI n
  have hpowI : ∀ m, Formalism.L2.Th1.C.IntPS (IntegralOrthonormalChange.intRing p) (h ^ m) := by
    intro m
    induction m with
    | zero => simpa using Formalism.L2.Th1.C.USideA.intPS_C (R := IntegralOrthonormalChange.intRing p) (one_mem _)
    | succ m ihm => rw [pow_succ]; exact Formalism.L2.Th1.C.USideA.intPS_mul ihm hhI
  have hint : ∀ n, b n ∈ IntegralOrthonormalChange.intRing p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rw [hb n]
      refine Subring.mul_mem _ ?_ ?_
      · show ‖(u ^ n)⁻¹‖ ≤ 1
        rw [norm_inv, norm_pow, h1, one_pow, inv_one]
      · exact Formalism.L2.Th1.C.USideA.intPS_sub Formalism.L2.Th1.C.USideA.intPS_X
          (Formalism.L2.Th1.C.USideA.intPS_sum _ fun m hm =>
            Formalism.L2.Th1.C.USideA.intPS_mul
              (Formalism.L2.Th1.C.USideA.intPS_C (ih m (Finset.mem_range.mp hm))) (hpowI m)) n
  refine ⟨PowerSeries.mk b, ?_, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hb0]
  · intro n
    rw [PowerSeries.coeff_mk]
    exact hint n
  · rw [PowerSeries.coeff_mk, hb1, norm_inv, h1, inv_one]
  · ext k
    rw [PowerSeries.coeff_subst' hH]
    simp only [PowerSeries.coeff_mk, smul_eq_mul]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (k + 1)) ?_]
    · have := hA (k + 1) k (Nat.lt_succ_self k)
      rw [map_sub, hcoeffP, sub_eq_zero] at this
      exact this.symm
    · intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hdk
      exact hd (by rw [hlow d k (by omega), mul_zero])

theorem exists_inv (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0)
    (hI : ∀ n, IsIntP (PowerSeries.coeff n h)) (h1 : ‖PowerSeries.coeff 1 h‖ = 1) :
    ∃ g : PowerSeries ℂ_[p], PowerSeries.constantCoeff g = 0 ∧ (∀ n, IsIntP (PowerSeries.coeff n g)) ∧
      h.subst g = PowerSeries.X := by
  obtain ⟨g, g0, gI, g1, hg⟩ := exists_integral_subst_inverse_of_unit_linear h h0 hI h1
  obtain ⟨k, k0, -, -, hk⟩ := exists_integral_subst_inverse_of_unit_linear g g0 gI g1
  have hG : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' g0
  have hH : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hkh : k = h := by
    have e1 : PowerSeries.subst h (PowerSeries.subst g k) = h := by
      rw [hk, PowerSeries.subst_X hH]
    rw [PowerSeries.subst_comp_subst_apply hG hH, hg, PowerSeries.X_subst] at e1
    exact e1
  refine ⟨g, g0, gI, ?_⟩
  rw [← hkh]
  exact hk

end ParameterChangeLemmas

open ParameterChangeLemmas IntegralOrthonormalChange

end Formalism.L2.KerInert

import Mathlib
import Formalism.PeriodIntegrals.BeConjNorm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.Development

noncomputable section

open Classical

namespace PI.BeConjNormW

open PI.PhNormUnits PI.PhNormUnits.UnitaryGroupMassFormula

variable {p : ℕ} [Fact p.Prime]

theorem coeff_one_subst (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.constantCoeff a = 0)
    (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst a f : PowerSeries ℂ_[p]) = PowerSeries.coeff 1 f * PowerSeries.coeff 1 a := by
  have hs : PowerSeries.HasSubst a := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.coeff 1 (PowerSeries.subst a f : PowerSeries ℂ_[p]) =
      ∑ᶠ k : ℕ, PowerSeries.coeff k f * PowerSeries.coeff 1 (a ^ k) :=
    (PowerSeries.coeff_subst hs f (Finsupp.single () 1)).trans (finsum_congr fun k => smul_eq_mul _ _)
  have hz : ∀ k, 2 ≤ k → PowerSeries.coeff 1 (a ^ k) = 0 := by
    intro k hk
    obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
    rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range 2)]
  · rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul, zero_add]
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hk (by rw [hz k (by omega), mul_zero])

private theorem coeff_zero_subst_of_constantCoeff_eq_zero (a f : PowerSeries ℂ_[p]) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.coeff 0 (PowerSeries.subst a f : PowerSeries ℂ_[p]) = PowerSeries.coeff 0 f := by
  have hs : PowerSeries.HasSubst a := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
  have h1 : PowerSeries.coeff 0 (PowerSeries.subst a f : PowerSeries ℂ_[p]) =
      ∑ᶠ k : ℕ, PowerSeries.coeff k f * PowerSeries.coeff 0 (a ^ k) :=
    (PowerSeries.coeff_subst hs f (Finsupp.single () 0)).trans (finsum_congr fun k => smul_eq_mul _ _)
  rw [h1, finsum_eq_sum_of_support_subset _ (s := Finset.range 1)]
  · simp
  · intro k hk
    rw [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hk
    obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr ha
    rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]

theorem linear_coeff_padic : LinCoeff := by
  intro q _ l ex hex hle c
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h := coeff_zero_subst_of_constantCoeff_eq_zero ex l hex
    rw [hle, PowerSeries.coeff_zero_X, PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    exact h.symm
  have hprod : PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 := by
    have h := coeff_one_subst ex l hex hl0
    rw [hle, PowerSeries.coeff_one_X] at h
    exact h.symm
  have hX0 : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℂ_[q]) = 0 := PowerSeries.constantCoeff_X
  have hsX0 : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_subst_of_constantCoeff_eq_zero _ _ hX0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hl0]
  have hsX1 : PowerSeries.coeff 1 (PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) =
      PowerSeries.coeff 1 l := by
    rw [coeff_one_subst _ _ hX0 hl0, PowerSeries.coeff_one_X, mul_one]
  have hc0 : PowerSeries.constantCoeff
      (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) = 0 := by
    rw [map_mul, hsX0, mul_zero]
  have key := coeff_one_subst
    (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) ex hc0 hex
  rw [PowerSeries.coeff_C_mul, hsX1] at key
  show PowerSeries.coeff 1 (PowerSeries.subst
    (PowerSeries.C c * PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[q]) l : PowerSeries ℂ_[q]) ex : PowerSeries ℂ_[q]) = c
  rw [key]
  linear_combination c * hprod

theorem core_of (hI : IntInv) (hL : LinCoeff) : StepCore := by
  intro p _ l ex ph hl0 hex0 hinv hph S hswap hadd hintS hIA hnm hdec hnorm hB
  have hE := norm_units_equivalence
  have hSub := norm_units_substitution
  have hC := norm_units_closed_form
  have hD := natCast_dense_p_adic
  have z0 := constantCoeff_var (p := p) (0 : Fin 2)
  have z1 := constantCoeff_var (p := p) (1 : Fin 2)
  have hInv : ∀ c : ℂ_[p], ‖c‖ = 1 → IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (mulBy l ex c⁻¹ (Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    intro c hc hcI
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hs0 : ∀ i : Unit, MvPowerSeries.constantCoeff
        ((fun _ => (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p])) i) = 0 :=
      fun _ => constantCoeff_formalSMul hex0 hinv _ _ (constantCoeff_var ())
    have hcomp := sb_mulBy (fun _ => (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p])) hs0 hex0 hinv c⁻¹
      (Xv ()) (constantCoeff_var ())
    rw [sb_X _ hs0] at hcomp
    rw [mulBy_mulBy hex0 hinv _ _ _ (constantCoeff_var ()), inv_mul_cancel₀ hc0, mulBy_one hex0 hinv _ (constantCoeff_var ())] at hcomp
    have key := hI p (mulBy l ex c (Xv ())) (mulBy l ex c⁻¹ (Xv ())) (constantCoeff_formalSMul hex0 hinv _ _ (constantCoeff_var ()))
      (constantCoeff_formalSMul hex0 hinv _ _ (constantCoeff_var ())) (by rw [hL p l ex hex0 hinv c]; exact hc) (fun n => hcI _) hcomp
    intro e
    have he : e = Finsupp.single () (e ()) := Finsupp.ext fun u => by cases u; simp
    unfold IsIntP
    rw [he]
    exact key (e ())
  have hU : ∀ β ∈ S, ‖β.1‖ = 1 → Simeq (be l ex ph (mulBy l ex β.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex β.2 (Xv 1))) := by
    intro β hβ h1
    obtain ⟨n, hn⟩ := hnm β hβ
    have hβ1 : β.1 ≠ 0 := by intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    have hw : IntegralMv (mulBy l ex β.1⁻¹ (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) :=
      int_mulBy_of hSub hex0 hinv β.1⁻¹ (hInv β.1 h1 (hintS β hβ)) _ z1 (int_X 1)
    exact units_iv hE hSub hex0 hinv β.1 β.2 hβ1 hw
      (sTrans hE (units_i hE hSub hex0 hinv hIA _ _ (hnorm β hβ))
        (units_ii hE hSub hC hD hex0 hinv hph hIA hB _ _ n hn))
  intro α hα
  obtain ⟨β, hβ, γ, hγ, hb1, hg1, rfl⟩ := hdec α hα
  have iM : ∀ c, IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]) → ∀ i : Fin 2,
      IntegralMv (mulBy l ex c (Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) :=
    fun c hc i => int_mulBy_of hSub hex0 hinv c hc _ (constantCoeff_var i) (int_X i)
  simp only [Prod.fst_add, Prod.snd_add]
  rw [← add_mulBy hex0 hinv _ _ _ z0, ← add_mulBy hex0 hinv _ _ _ z1]
  refine sTrans hE (be_add_left hSub hex0 hinv hB _ _ _ (constantCoeff_formalSMul hex0 hinv _ _ z0) (constantCoeff_formalSMul hex0 hinv _ _ z0)
    z1 (iM _ (hintS β hβ) 0) (iM _ (hintS γ hγ) 0) (int_X 1)) ?_
  refine sTrans hE (sAdd hE (hU β hβ hb1) (hU γ hγ hg1)) ?_
  exact sSymm hE (be_add_right hSub hex0 hinv hB _ _ _ (constantCoeff_formalSMul hex0 hinv _ _ z1) (constantCoeff_formalSMul hex0 hinv _ _ z1) z0
    (iM β.2 (hintS β.swap (hswap β hβ)) 1) (iM γ.2 (hintS γ.swap (hswap γ hγ)) 1) (int_X 0))

theorem beConjNorm_of_intInv (hI : IntInv) : PI.BeConjNorm.BeConjNorm :=
  beConjNorm_of (core_of hI linear_coeff_padic)

end PI.BeConjNormW

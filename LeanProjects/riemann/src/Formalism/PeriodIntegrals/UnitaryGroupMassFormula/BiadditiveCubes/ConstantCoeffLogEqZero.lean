import Mathlib
import Formalism.PeriodIntegrals.BiaddOfCube

noncomputable section

open Classical

namespace PI.BiaddOfCubeWork

open PI.BiaddOfCube

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_log_eq_zero {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X) :
    PowerSeries.constantCoeff l = 0 := by
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hex'
  have h1 := PowerSeries.constantCoeff_subst (R := ℂ_[p]) hs l
  rw [h, finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero]),
    pow_zero, map_one, smul_eq_mul, mul_one] at h1
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← h1]
  exact PowerSeries.constantCoeff_X

variable {σ : Type*}

theorem subst_subst_log {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X)
    (y : MvPowerSeries σ ℂ_[p]) (hy : MvPowerSeries.constantCoeff y = 0) :
    PowerSeries.subst (PowerSeries.subst y ex) l = y := by
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hex')
    (PowerSeries.HasSubst.of_constantCoeff_zero hy), h,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hy)]

theorem constantCoeff_subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0)
    (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  exact PowerSeries.constantCoeff_subst_eq_zero ha f hf

theorem add_comm' (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) :
    add l ex a b = add l ex b a := by
  show PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex =
    PowerSeries.subst (PowerSeries.subst b l + PowerSeries.subst a l) ex
  rw [add_comm]

theorem add_assoc' {l ex : PowerSeries ℂ_[p]}
    (hex : PowerSeries.constantCoeff ex = 0) (h : PowerSeries.subst ex l = PowerSeries.X)
    (a b c : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (hc : MvPowerSeries.constantCoeff c = 0) :
    add l ex (add l ex a b) c = add l ex a (add l ex b c) := by
  have hl := constantCoeff_log_eq_zero hex h
  have hla := constantCoeff_subst_zero hl a ha
  have hlb := constantCoeff_subst_zero hl b hb
  have hlc := constantCoeff_subst_zero hl c hc
  show PowerSeries.subst (PowerSeries.subst (add l ex a b) l + PowerSeries.subst c l) ex =
    PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst (add l ex b c) l) ex
  rw [show add l ex a b = PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex from rfl,
    subst_subst_log hex h _ (by rw [map_add, hla, hlb, add_zero]),
    show add l ex b c = PowerSeries.subst (PowerSeries.subst b l + PowerSeries.subst c l) ex from rfl,
    subst_subst_log hex h _ (by rw [map_add, hlb, hlc, add_zero]), add_assoc]

theorem simeq_of_sub_eq {f g f' g' : MvPowerSeries σ ℂ_[p]} (e : f - g = f' - g')
    (hs : Simeq f' g') : Simeq f g := by
  show MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))
  rw [e]
  exact hs

theorem cc_Xv (i : Fin 3) : MvPowerSeries.constantCoeff (Xv (p := p) i) = 0 := by
  exact MvPowerSeries.constantCoeff_X i

theorem target : Target := by
  intro p _ l ex ph hex h hC
  constructor
  · refine simeq_of_sub_eq ?_ hC
    simp only [be]
    rw [add_comm' l ex (Xv 2) (Xv 0)]
    ring
  · refine simeq_of_sub_eq ?_ hC
    simp only [be]
    rw [add_comm' l ex (Xv 2) (Xv 0),
      add_assoc' hex h (Xv 0) (Xv 1) (Xv 2) (cc_Xv 0) (cc_Xv 1) (cc_Xv 2)]
    ring

end PI.BiaddOfCubeWork

import Formalism.EllipticTorsion.WChordSeries

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace WeierstrassPointSeriesTail

def wTail {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R) : PowerSeries R :=
  C W.a₁ * X * w + C W.a₂ * X ^ 2 * w + C W.a₃ * w ^ 2 + C W.a₄ * X * w ^ 2 + C W.a₆ * w ^ 3

theorem wTail_dvd {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (k : ℕ) (hk : 1 ≤ k) (h : (X : PowerSeries R) ^ k ∣ w) :
    (X : PowerSeries R) ^ (k + 1) ∣ wTail W w := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨u, rfl⟩ := h
  refine ⟨C W.a₁ * u + C W.a₂ * X * u + C W.a₃ * X ^ j * u ^ 2 + C W.a₄ * X ^ (j + 1) * u ^ 2 +
    C W.a₆ * X ^ (2 * j + 1) * u ^ 3, ?_⟩
  unfold wTail
  ring

theorem factor {R : Type u} [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R)
    (hw : WFixed W w) : ∃ e : PowerSeries R, w = X ^ 3 * (1 + X * e) := by
  have hsplit : w = X ^ 3 + wTail W w := by
    unfold wTail
    conv_lhs => rw [hw.2]
    ring
  have d1 : (X : PowerSeries R) ^ 1 ∣ w := by
    rw [pow_one, PowerSeries.X_dvd_iff]
    exact hw.1
  have d2 : (X : PowerSeries R) ^ 2 ∣ w := by
    rw [hsplit]
    exact dvd_add (pow_dvd_pow X (by norm_num)) (wTail_dvd W w 1 le_rfl d1)
  have d3 : (X : PowerSeries R) ^ 3 ∣ w := by
    rw [hsplit]
    exact dvd_add dvd_rfl (wTail_dvd W w 2 (by norm_num) d2)
  obtain ⟨e, he⟩ := wTail_dvd W w 3 (by norm_num) d3
  exact ⟨e, by rw [hsplit, he]; ring⟩

end WeierstrassPointSeriesTail

open WeierstrassPointSeriesTail in
theorem wSeriesNonsingularPoint_holds : WPoint := by
  intro K _ W w hw σ _ s hs0 hs
  have : IsDomain (MvPowerSeries σ K) := NoZeroDivisors.to_isDomain _
  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs0
  have hE : w.subst s = s ^ 3 + MvPowerSeries.C W.a₁ * s * w.subst s +
      MvPowerSeries.C W.a₂ * s ^ 2 * w.subst s + MvPowerSeries.C W.a₃ * (w.subst s) ^ 2 +
      MvPowerSeries.C W.a₄ * s * (w.subst s) ^ 2 + MvPowerSeries.C W.a₆ * (w.subst s) ^ 3 := by
    conv_lhs => rw [hw.2]
    simp only [PowerSeries.subst_add hsub, PowerSeries.subst_mul hsub, PowerSeries.subst_pow hsub,
      PowerSeries.subst_X hsub, PowerSeries.subst_C]
  obtain ⟨e, he⟩ := factor W w hw
  have hfac : w.subst s = s ^ 3 * (1 + s * e.subst s) := by
    rw [← PowerSeries.coe_substAlgHom hsub, he]
    simp [PowerSeries.substAlgHom_X]
  have hwc : MvPowerSeries.constantCoeff (w.subst s) = 0 := by
    rw [hfac]
    simp [hs0]
  have hws0 : w.subst s ≠ 0 := by
    rw [hfac]
    refine mul_ne_zero (pow_ne_zero 3 hs) (fun h0 => ?_)
    have := congrArg MvPowerSeries.constantCoeff h0
    simp [hs0] at this
  have hinj := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
  have hV : algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hws0
  have hC : ∀ a : K, algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
      (MvPowerSeries.C a) = algebraMap K (FractionRing (MvPowerSeries σ K)) a := fun a =>
    (IsScalarTower.algebraMap_apply K (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) a).symm
  have hE' := congrArg (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))) hE
  simp only [map_add, map_mul, map_pow, hC] at hE'
  have hx : xOf w s * algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) =
      algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s := by
    simp only [xOf]
    exact div_mul_cancel₀ _ hV
  have hy : yOf w s * algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s) =
      -1 := by
    simp only [yOf]
    rw [div_mul_cancel₀ _ hV]
  set Z := algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) s
  set V := algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) (w.subst s)
  set x := xOf w s
  set y := yOf w s
  set A₁ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₁
  set A₂ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₂
  set A₃ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₃
  set A₄ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₄
  set A₆ := algebraMap K (FractionRing (MvPowerSeries σ K)) W.a₆
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  refine ⟨?_, ?_⟩
  · apply mul_left_cancel₀ (pow_ne_zero 3 hV)
    linear_combination hE' + (V * (y * V - 1) + A₁ * V * Z + A₃ * V ^ 2) * hy +
      (A₁ * V * (y * V) - ((x * V) ^ 2 + (x * V) * Z + Z ^ 2) - A₂ * V * (x * V + Z) - A₄ * V ^ 2) * hx
  · by_contra hcon
    push Not at hcon
    obtain ⟨hP, hQ⟩ := hcon
    have hD0 : (1 - MvPowerSeries.C W.a₁ * s - 2 * MvPowerSeries.C W.a₃ * w.subst s -
        MvPowerSeries.C W.a₂ * s ^ 2 - 2 * MvPowerSeries.C W.a₄ * s * w.subst s -
        3 * MvPowerSeries.C W.a₆ * (w.subst s) ^ 2 : MvPowerSeries σ K) ≠ 0 := by
      intro h0
      have := congrArg MvPowerSeries.constantCoeff h0
      simp [hs0, hwc] at this
    apply hD0
    apply hinj
    rw [map_zero]
    apply (mul_eq_zero.mp _).resolve_right hV
    simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, hC]
    linear_combination V ^ 2 * hQ - Z * V ^ 2 * hP + 3 * hE' + (-2 * V + Z * A₁ * V) * hy +
      (-A₁ * V - 3 * Z * (x * V + Z) - 2 * A₂ * Z * V) * hx

end Formalism.ELL

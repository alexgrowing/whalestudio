import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReadingOver

open GlobalTheory.GoodPts

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p])

theorem norm_le_one_of_valuation_le_one {x : F} (hx : (placeAt φ).valuation F x ≤ 1) : ‖φ x‖ ≤ 1 := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (placeAt φ) x hx
  have hd : ‖φ ((d : 𝓞 F) : F)‖ = 1 := le_antisymm (norm_int_le_one φ _) (not_lt.1 d.2)
  have h2 := congrArg (fun t => ‖φ t‖) hnd
  simp only [map_mul, norm_mul] at h2
  have h3 : ‖φ x‖ * ‖φ ((d : 𝓞 F) : F)‖ = ‖φ (n : F)‖ := h2
  rw [hd, mul_one] at h3
  rw [h3]; exact norm_int_le_one φ n

variable (T : CDVR)

theorem valV_le_one_of_inV {x : T.Fr} (hx : InV T x) : valV T.V x ≤ 1 := by
  obtain ⟨v, rfl⟩ := hx
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one _ _

theorem inV_of_valV_le_one {x : T.Fr} (hx : valV T.V x ≤ 1) : InV T x := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer
    (IsDiscreteValuationRing.maximalIdeal T.V) x hx
  have hu : IsUnit (d : T.V) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  refine ⟨n * ↑hu.unit⁻¹, ?_⟩
  rw [map_mul, ← hnd, mul_assoc, ← map_mul, hu.mul_val_inv, map_one, mul_one]

theorem vV_zpow {x : T.Fr} (n : ℤ) : vV T.V (x ^ n) = n * vV T.V x := by
  simp only [vV, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

variable {T}

theorem overLa_placeAt_of_isReading {io : F →+* T.Fr} {k : T.Fr →+* ℂ_[p]} (hR : IsReading φ T io k) :
    ∃ e : ℕ, OverLa (placeAt φ) T.V io e := by
  set P := placeAt φ with hP
  have key : ∀ y : T.Fr, valV T.V y ≤ 1 ↔ ‖k y‖ ≤ 1 := fun y =>
    ⟨fun h => (hR.int y).2 (inV_of_valV_le_one T h), fun h => valV_le_one_of_inV T ((hR.int y).1 h)⟩
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ1 : P.intValuation π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπn : ‖φ (π : F)‖ < 1 := (mem_placeAt φ π).1 ((P.intValuation_lt_one_iff_mem π).1 hπ1)
  have hπ0 : (π : F) ≠ 0 := by
    intro h
    have h' : π = 0 := by exact_mod_cast h
    rw [h', map_zero] at hπ
    exact WithZero.exp_ne_zero.symm hπ
  have hνπ : P.valuation F (π : F) = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuation_of_algebraMap P π
  set x := io (π : F) with hx
  have hx0 : x ≠ 0 := (map_ne_zero io).2 hπ0
  have hkx : ‖k x‖ < 1 := by rw [hx, hR.comp]; exact hπn
  have hvx1 : valV T.V x < 1 := by
    refine lt_of_le_of_ne ((key x).2 hkx.le) fun h1 => ?_
    have h2 : valV T.V x⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
    have h3 := (key _).1 h2
    rw [map_inv₀, norm_inv] at h3
    have h4 : 0 < ‖k x‖ := norm_pos_iff.2 ((map_ne_zero k).2 hx0)
    exact absurd h3 (not_le.2 ((one_lt_inv₀ h4).2 hkx))
  have hvx : 0 < vV T.V x := by
    have h := (WithZero.log_lt_log (valV_ne_zero hx0) one_ne_zero).2 hvx1
    rw [WithZero.log_one] at h
    simp only [vV]; omega
  refine ⟨(vV T.V x).toNat, by omega, fun a => ?_⟩
  by_cases ha : a = 0
  · subst ha; simp [vV, vLa]
  set n := vLa P a with hn
  set b := a * (π : F) ^ (-n) with hb
  have hb0 : b ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hπ0)
  have hνa : P.valuation F a = WithZero.exp (-n) := by
    rw [hn, vLa, neg_neg, WithZero.exp_log ((P.valuation F).ne_zero_iff.2 ha)]
  have hνb : P.valuation F b = 1 := by
    rw [hb, map_mul, map_zpow₀, hνa, hνπ, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hkb : ‖k (io b)‖ ≤ 1 := by rw [hR.comp]; exact norm_le_one_of_valuation_le_one φ hνb.le
  have hkb' : ‖k (io b)⁻¹‖ ≤ 1 := by
    rw [← map_inv₀, hR.comp]
    exact norm_le_one_of_valuation_le_one φ (by rw [map_inv₀, hνb, inv_one])
  have hvb1 : valV T.V (io b) = 1 := by
    have h1 := (key _).2 hkb
    have h2 := (key _).2 hkb'
    rw [map_inv₀] at h2
    have hv0 : valV T.V (io b) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 hb0)
    have h3 : valV T.V (io b) * (valV T.V (io b))⁻¹ ≤ valV T.V (io b) * 1 := mul_le_mul_right h2 _
    rw [mul_inv_cancel₀ hv0, mul_one] at h3
    exact le_antisymm h1 h3
  have hvb : vV T.V (io b) = 0 := by simp [vV, hvb1]
  have hab : io a = io b * x ^ n := by
    rw [hx, ← map_zpow₀, ← map_mul, hb, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hab, vV_mul ((map_ne_zero io).2 hb0) (zpow_ne_zero _ hx0), hvb, vV_zpow, Int.toNat_of_nonneg hvx.le]
  ring

theorem overLa_placeAt : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR)
    (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∃ e : ℕ, OverLa (placeAt φ) T.V io e :=
  fun _ _ _ _ _ φ _ _ _ hR => overLa_placeAt_of_isReading φ hR

end GlobalTheory.ReadingOver

end

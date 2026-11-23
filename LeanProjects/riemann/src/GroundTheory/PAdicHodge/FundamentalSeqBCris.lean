import Mathlib
import GroundTheory.PAdicHodge.FundamentalSeqFixed
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

section Abstract

variable {S R E D : Type*} [CommRing S] [CommRing R] [CommRing E] [CommRing D]

theorem map_eq_map_pow_mul_of_fixed (g : S →+* R) (f : R →+* R) (ψ : S → S) {y c₀ : S} {t c x : R}
    {n : ℕ} (hc : g c₀ = c) (hy : g y = t ^ n * x) (hx : f x = x)
    (h : g (ψ^[1] y) = (c ^ 1 * t) ^ n * f^[1] x) : g (ψ y) = g (c₀ ^ n * y) := by
  rw [Function.iterate_one, Function.iterate_one, hx] at h
  rw [h, map_mul, map_pow, hc, hy]
  ring

theorem eq_map_of_map_eq_pow_mul (g : S →+* R) {y a t₀ : S} {x : R} {n : ℕ}
    (ht : IsUnit (g t₀)) (hy : g y = g t₀ ^ n * x) (hq : y = a * t₀ ^ n) : x = g a :=
  (ht.pow n).mul_left_cancel (by rw [← hy, hq, map_mul, map_pow, mul_comm])

theorem exists_pow_mul_eq {u : R} (hu : IsUnit u) (n : ℕ) (z : R) : ∃ x : R, u ^ n * x = z :=
  ⟨↑(hu.unit⁻¹) ^ n * z, by rw [← mul_assoc, ← mul_pow, IsUnit.mul_val_inv, one_pow, one_mul]⟩

theorem map_eq_self_of_pow_mul_eq (g : S →+* R) (f : R →+* R) (ψ : S → S) {y c₀ : S} {t c x : R}
    {n : ℕ} (hc : g c₀ = c) (hu : IsUnit (g c₀ * t)) (hx : t ^ n * x = g y) (hψ : ψ y = c₀ ^ n * y)
    (h : g (ψ^[1] y) = (c ^ 1 * t) ^ n * f^[1] x) : f x = x := by
  rw [hc] at hu
  rw [Function.iterate_one, Function.iterate_one, hψ, map_mul, map_pow, hc, ← hx, pow_one] at h
  refine (hu.pow n).mul_left_cancel ?_
  rw [← h]
  ring

theorem map_pow_mul_eq_of_eq (ι : R →+* E) {t x r : R} {τ e : E} {n : ℕ} (ht : ι t = τ)
    (h : t ^ n * x = r) (hr : ι r = e) : τ ^ n * ι x = e := by
  rw [← ht, ← map_pow, ← map_mul, h, hr]

theorem sub_eq_map_of_pow_mul {F : Type*} [Field F] (j : D →+* F) {T w c a : D} {z X : F} {n : ℕ}
    (hT : j T ≠ 0) (hX : j T ^ n * X = j a) (hz : z * j T ^ n = j w) (hc : c * T ^ n = a - w) :
    X - z = j c := by
  apply mul_right_cancel₀ (pow_ne_zero n hT)
  rw [sub_mul, mul_comm X, hX, hz, ← map_sub, ← hc, map_mul, map_pow]

theorem map_add_eq_of_eq (f : R →+* R) {x y : R} (hx : f x = x) (hy : f y = y) :
    f (x + y) = x + y := by
  rw [map_add, hx, hy]

theorem map_mul_eq_of_eq (f : R →+* R) {a x : R} (ha : f a = a) (hx : f x = x) : f (a * x) = a * x := by
  rw [map_mul, ha, hx]

end Abstract

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

theorem phiB_algebraMap_padic' (q : ℚ_[p]) :
    phiB hε (algebraMap ℚ_[p] (BCris hε) q) = algebraMap ℚ_[p] (BCris hε) q :=
  phiB_algebraMap_padic hε q

set_option maxHeartbeats 1600000 in

theorem iotaB_algebraMap_padic (q : ℚ_[p]) :
    iotaB hε hζ (algebraMap ℚ_[p] (BCris hε) q) = algebraMap ℚ_[p] 𝔹dR q := by
  rw [algebraMap_padic_bCris, iotaB_algebraMap, iotaPlus_algebraMap_padic,
    ← IsScalarTower.algebraMap_apply]

set_option maxHeartbeats 1600000 in

theorem exists_eq_algebraMap_of_phiB_eq {x : BCris hε} (hφ : phiB hε x = x)
    (hx : iotaB hε hζ x ∈ (algebraMap 𝔹 𝔹dR).range) :
    ∃ q : ℚ_[p], x = algebraMap ℚ_[p] (BCris hε) q := by
  obtain ⟨n, y, hy⟩ := exists_algebraMap_eq_periodTCris_pow_mul hε x
  have hφy : phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ n * y :=
    algebraMap_bCrisPlus_bCris_injective hε hζ (map_eq_map_pow_mul_of_fixed
      (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (phiB hε) (phiPlus ℂ_[p] p) (map_natCast _ p) hy
      hφ (algebraMap_iterate_phiPlus_eq hε hy 1))
  obtain ⟨b, hb⟩ := hx
  have hιy : iotaPlus ℂ_[p] p y = iota ℂ_[p] p (periodT hε) ^ n * b :=
    eq_pow_mul_of_map_eq (iotaB hε hζ) (algebraMap 𝔹 𝔹dR) (IsFractionRing.injective 𝔹 𝔹dR)
      ((iotaB_algebraMap hε hζ y).symm.trans (congrArg _ hy)) (iotaB_periodTCris hε hζ) hb.symm
  have hιy' : iotaPlus ℂ_[p] p y ∈ Ideal.span {fontaineT ε hε ^ n} := by
    rw [hιy, iota_periodT, Ideal.mem_span_singleton']
    exact ⟨b, mul_comm _ _⟩
  obtain ⟨q, hq⟩ := exists_eq_algebraMap_mul_pow_of_phiPlus_eq hε hζ n hφy hιy'
  exact ⟨q, eq_map_of_map_eq_pow_mul (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε))
    (isUnit_periodTCris hε) hy hq⟩

set_option maxHeartbeats 1600000 in

theorem iotaB_mem_range_iff {x : BCris hε} (hφ : phiB hε x = x) :
    iotaB hε hζ x ∈ (algebraMap 𝔹 𝔹dR).range ↔ ∃ q : ℚ_[p], x = algebraMap ℚ_[p] (BCris hε) q := by
  refine ⟨exists_eq_algebraMap_of_phiB_eq hε hζ hφ, ?_⟩
  rintro ⟨q, rfl⟩
  exact ⟨algebraMap ℚ_[p] 𝔹 q, ((iotaB_algebraMap_padic hε hζ q).trans
    (IsScalarTower.algebraMap_apply ℚ_[p] 𝔹 𝔹dR q)).symm⟩

include hζ in
set_option maxHeartbeats 1600000 in

theorem exists_mul_pow_fontaineT_eq (z : 𝔹dR) :
    ∃ (n : ℕ) (w : 𝔹), z * algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ n = algebraMap 𝔹 𝔹dR w := by
  have := IsPerfectoidField.isLocalization_away_bDeRham (maximalIdeal_eq_span_fontaineT hε hζ)
  obtain ⟨⟨w, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (fontaineT ε hε)) z
  obtain ⟨n, hn⟩ := s.2
  simp only at hn hs
  rw [← hn] at hs
  refine ⟨n, w, ?_⟩
  rw [← map_pow]
  exact hs

set_option maxHeartbeats 1600000 in

theorem exists_phiB_eq_pow_mul_eq {y : BCrisPlus ℂ_[p] p} {n : ℕ}
    (hy : phiPlus ℂ_[p] p y = (p : BCrisPlus ℂ_[p] p) ^ n * y) :
    ∃ x : BCris hε, phiB hε x = x ∧
      periodTCris hε ^ n * x = algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y := by
  obtain ⟨x, hx⟩ := exists_pow_mul_eq (isUnit_periodTCris hε) n
    (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) y)
  have hpT : IsUnit (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε) (p : BCrisPlus ℂ_[p] p) *
      periodTCris hε) :=
    (isUnit_p_bCrisPlus.map (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε))).mul (isUnit_periodTCris hε)
  exact ⟨x, map_eq_self_of_pow_mul_eq (algebraMap (BCrisPlus ℂ_[p] p) (BCris hε)) (phiB hε)
    (phiPlus ℂ_[p] p) (map_natCast _ p) hpT hx hy (algebraMap_iterate_phiPlus_eq hε hx.symm 1), hx⟩

set_option maxHeartbeats 12000000 in

theorem exists_phiB_eq_iotaB_sub_mem (z : 𝔹dR) :
    ∃ x : BCris hε, phiB hε x = x ∧ iotaB hε hζ x - z ∈ (algebraMap 𝔹 𝔹dR).range := by
  obtain ⟨n, w, hs⟩ := exists_mul_pow_fontaineT_eq hε hζ z
  obtain ⟨y, hy, hyw⟩ := exists_phiPlus_eq_pow_iotaPlus_sub_mem hε hζ (m := n) (n := n) le_rfl w
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hyw
  obtain ⟨x, hfix, hx⟩ := exists_phiB_eq_pow_mul_eq hε hy
  have hT0 : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective 𝔹 𝔹dR)).2 (fontaineT_ne_zero hε hζ)
  have hX : algebraMap 𝔹 𝔹dR (fontaineT ε hε) ^ n * iotaB hε hζ x =
      algebraMap 𝔹 𝔹dR (iotaPlus ℂ_[p] p y) :=
    map_pow_mul_eq_of_eq (iotaB hε hζ) ((iotaB_periodTCris hε hζ).trans
      (congrArg _ (iota_periodT hε))) hx (iotaB_algebraMap hε hζ y)
  exact ⟨x, hfix, RingHom.mem_range.2 ⟨c, (sub_eq_map_of_pow_mul (algebraMap 𝔹 𝔹dR) hT0 hX hs hc).symm⟩⟩

end ACris

end GroundTheory.PAdicHodge

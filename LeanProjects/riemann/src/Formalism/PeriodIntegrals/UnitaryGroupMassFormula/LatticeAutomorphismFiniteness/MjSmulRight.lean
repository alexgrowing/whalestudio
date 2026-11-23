import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.MulVecMapInjective

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

def mj (z x y : S.V) : E := S.hT x y - 2 / S.hT z z * (S.hT x z * S.hT z y)

variable {S}

theorem star_hzz (z : S.V) : star (S.hT z z) = S.hT z z := by
  have h := S.herm.eq z z
  rwa [starRingEnd_apply] at h

theorem mj_add_left (z x x' y : S.V) : mj S z (x + x') y = mj S z x y + mj S z x' y := by
  simp only [mj, map_add, LinearMap.add_apply]
  ring

theorem mj_smul_left (z : S.V) (c : E) (x y : S.V) : mj S z (c • x) y = star c * mj S z x y := by
  simp only [mj, LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]
  ring

theorem mj_add_right (z x y y' : S.V) : mj S z x (y + y') = mj S z x y + mj S z x y' := by
  simp only [mj, map_add]
  ring

theorem mj_smul_right (z : S.V) (c : E) (x y : S.V) : mj S z x (c • y) = c * mj S z x y := by
  simp only [mj, map_smul, smul_eq_mul]
  ring

theorem mj_swap (z x y : S.V) : mj S z y x = star (mj S z x y) := by
  have hs : ∀ a b : S.V, star (S.hT a b) = S.hT b a := fun a b => by
    have h := S.herm.eq a b
    rwa [starRingEnd_apply] at h
  simp only [mj, star_sub, star_mul', star_div₀, hs, star_ofNat]
  ring

theorem mj_self_star (z x : S.V) : star (mj S z x x) = mj S z x x := (mj_swap z x x).symm

theorem tau_real {τ : E →+* ℂ} (hstar : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) {a : E}
    (ha : star a = a) : τ a = ((τ a).re : ℂ) := by
  have h := hstar a
  rw [ha] at h
  exact (Complex.conj_eq_iff_re.1 h.symm).symm

theorem tau_normSq {τ : E →+* ℂ} (hstar : ∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) (c : E) :
    τ (star c * c) = (Complex.normSq (τ c) : ℂ) := by
  rw [map_mul, hstar, Complex.normSq_eq_conj_mul_self]

section Pos

variable (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) (τ : E →+* ℂ)
  (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
  (hzz : (τ (S.hT z z)).re < 0)
  (hpos : ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
include hstar hPX hzP hzz hpos

theorem mj_pos (y : S.V) (hy : y ∈ P) :
    0 ≤ (τ (mj S z y y)).re ∧ ((τ (mj S z y y)).re = 0 → y ∈ X) := by
  have hzz0 : S.hT z z ≠ 0 := by
    intro h; rw [h, map_zero] at hzz; simp at hzz
  set c := S.hT z y / S.hT z z with hc
  set y0 := y - c • z with hy0def
  have h1 : S.hT z y0 = 0 := by
    simp only [y0, map_sub, LinearMap.map_smul, smul_eq_mul, c]
    field_simp; ring
  have hy0 : y0 ∈ P := P.sub_mem hy (P.smul_mem c hzP)
  have h2 : S.hT y0 z = 0 := by rw [herm_swap, h1, star_zero]
  have hm : mj S z y y = S.hT y0 y0 - star c * c * S.hT z z := by
    have hyy : y = y0 + c • z := by simp [y0]
    rw [hyy]
    simp only [mj, map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, h1, h2, starRingEnd_apply, RingHom.id_apply]
    field_simp
    ring
  have hq : 0 ≤ (τ (S.hT y0 y0)).re ∧ ((τ (S.hT y0 y0)).re = 0 → y0 ∈ X) := by
    by_cases hX : y0 ∈ X
    · have : S.hT y0 y0 = 0 := hPX y0 hX y0 hy0
      simp [this, hX]
    · have := hpos y0 hy0 h1 hX
      exact ⟨this.le, fun h => absurd h this.ne'⟩
  have hτ : (τ (mj S z y y)).re = (τ (S.hT y0 y0)).re - Complex.normSq (τ c) * (τ (S.hT z z)).re := by
    rw [hm, map_sub, map_mul, tau_normSq (hstar τ), Complex.sub_re, Complex.re_ofReal_mul]
  have hns := Complex.normSq_nonneg (τ c)
  refine ⟨by rw [hτ]; nlinarith, fun h0 => ?_⟩
  rw [hτ] at h0
  have hA : Complex.normSq (τ c) * (τ (S.hT z z)).re = 0 := by nlinarith
  have hB : (τ (S.hT y0 y0)).re = 0 := by nlinarith
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hA with h | h
    · exact τ.injective (by rw [Complex.normSq_eq_zero.mp h, map_zero])
    · exact absurd h hzz.ne
  have : y = y0 := by simp [y0, hc0]
  rw [this]; exact hq.2 hB

theorem mj_cs (x y : S.V) (hx : x ∈ P) (hy : y ∈ P) :
    Complex.normSq (τ (mj S z x y)) ≤ (τ (mj S z x x)).re * (τ (mj S z y y)).re := by
  have hnn : ∀ s : E, 0 ≤ (τ (mj S z (s • x + y) (s • x + y))).re := fun s =>
    (mj_pos hstar τ X P hPX z hzP hzz hpos _ (P.add_mem (P.smul_mem s hx) hy)).1
  have hexp : ∀ s : E, mj S z (s • x + y) (s • x + y) =
      star s * s * mj S z x x + star s * mj S z x y + s * star (mj S z x y) + mj S z y y := by
    intro s
    rw [mj_add_left, mj_add_right, mj_add_right, mj_smul_left, mj_smul_left, mj_smul_right,
      mj_smul_right, mj_swap z x y]
    ring
  have hareal := tau_real (hstar τ) (mj_self_star z x)
  have ha0 := (mj_pos hstar τ X P hPX z hzP hzz hpos x hx).1
  rcases ha0.lt_or_eq with hapos | hazero
  · have hane : mj S z x x ≠ 0 := by
      intro h; rw [h, map_zero] at hapos; simp at hapos
    have h := hnn (-(mj S z x y) / mj S z x x)
    rw [hexp] at h
    have hval : star (-(mj S z x y) / mj S z x x) * (-(mj S z x y) / mj S z x x) * mj S z x x +
        star (-(mj S z x y) / mj S z x x) * mj S z x y +
        (-(mj S z x y) / mj S z x x) * star (mj S z x y) + mj S z y y =
        mj S z y y - (star (mj S z x y) * mj S z x y) / mj S z x x := by
      rw [star_div₀, star_neg, mj_self_star]
      field_simp
      ring
    rw [hval, map_sub, map_div₀, tau_normSq (hstar τ), hareal, Complex.sub_re] at h
    rw [← Complex.ofReal_div, Complex.ofReal_re] at h
    rw [sub_nonneg, div_le_iff₀ hapos] at h
    linarith
  · have hτa : τ (mj S z x x) = 0 := by rw [hareal, ← hazero]; simp
    have ha : mj S z x x = 0 := τ.injective (by rw [hτa, map_zero])
    rw [← hazero, zero_mul]
    by_contra hlt
    have hpos' : 0 < Complex.normSq (τ (mj S z x y)) := lt_of_not_ge hlt
    obtain ⟨N, hN⟩ := exists_nat_gt ((τ (mj S z y y)).re / (2 * Complex.normSq (τ (mj S z x y))))
    have h := hnn (-(N : E) * mj S z x y)
    rw [hexp, ha] at h
    have hval : star (-(N : E) * mj S z x y) * (-(N : E) * mj S z x y) * 0 +
        star (-(N : E) * mj S z x y) * mj S z x y +
        (-(N : E) * mj S z x y) * star (mj S z x y) + mj S z y y =
        mj S z y y - (2 * (N : E)) * (star (mj S z x y) * mj S z x y) := by
      rw [star_mul, star_neg, star_natCast]
      ring
    rw [hval, map_sub, map_mul, tau_normSq (hstar τ), Complex.sub_re] at h
    have h2 : (τ (2 * (N : E))) = ((2 * (N : ℝ) : ℝ) : ℂ) := by
      rw [map_mul, map_natCast, map_ofNat]; push_cast; ring
    rw [h2, ← Complex.ofReal_mul, Complex.ofReal_re] at h
    rw [div_lt_iff₀ (by positivity)] at hN
    nlinarith

end Pos

end PI.AutLzFinite.SlopeTestRemainingChoices

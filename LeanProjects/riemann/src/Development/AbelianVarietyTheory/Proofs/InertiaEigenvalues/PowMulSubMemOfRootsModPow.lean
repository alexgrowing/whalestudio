import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem pow_mul_sub_mem_of_roots_mod_pow :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (p : Polynomial R) (x y b lam : R) (n : ℕ),
      p.eval x ∈ I ^ n → p.eval y ∈ I ^ n → x - y ∈ I →
        b * (Polynomial.derivative p).eval x - lam ∈ I → lam ^ n * (x - y) ∈ I ^ n := by
  intro R _ I p x y b lam n hx hy hxy hb
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion p x (y - x)
  have hy' : x + (y - x) = y := by ring
  rw [hy'] at hk
  obtain ⟨d, hdd⟩ : ∃ d, d = y - x := ⟨_, rfl⟩
  rw [← hdd] at hk
  have hd : d ∈ I := by
    have e : d = -(x - y) := by rw [hdd]; ring
    rw [e]; exact I.neg_mem hxy
  obtain ⟨h, hh⟩ : ∃ h, h = (Polynomial.derivative p).eval x + k * d := ⟨_, rfl⟩
  have hdh : d * h ∈ I ^ n := by
    have e : d * h = p.eval y - p.eval x := by rw [hk, hh]; ring
    rw [e]; exact sub_mem hy hx
  obtain ⟨j, hjj⟩ : ∃ j, j = b * h - lam := ⟨_, rfl⟩
  have hj : j ∈ I := by
    have e : j = (b * (Polynomial.derivative p).eval x - lam) + b * k * d := by
      rw [hjj, hh]; ring
    rw [e]; exact add_mem hb (I.mul_mem_left _ hd)
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow lam (-j) n
  have e : lam ^ n * (x - y) = -(b * q * (d * h)) - (-j) ^ n * d := by
    have e1 : lam ^ n = (lam - -j) * q + (-j) ^ n := by rw [← hq]; ring
    have e2 : lam - -j = b * h := by rw [hjj]; ring
    have e3 : x - y = -d := by rw [hdd]; ring
    rw [e1, e2, e3]; ring
  rw [e]
  exact sub_mem (neg_mem (Ideal.mul_mem_left _ _ hdh))
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (neg_mem hj) n))

end GlobalTheory

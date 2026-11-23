import Mathlib

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

def mI (hv : v.Integers R) : Ideal R where
  carrier := {r | v (algebraMap R C r) < 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
    calc v (algebraMap R C c) * v (algebraMap R C x) ≤ 1 * v (algebraMap R C x) :=
          mul_le_mul_of_nonneg_right (hv.map_le_one c) zero_le
      _ < 1 := by rwa [one_mul]

theorem mem_mI (hv : v.Integers R) (r : R) : r ∈ mI hv ↔ v (algebraMap R C r) < 1 := Iff.rfl

theorem v_eq_one_iff (hv : v.Integers R) (r : R) : v (algebraMap R C r) = 1 ↔ r ∉ mI hv := by
  rw [mem_mI, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm (hv.map_le_one r) h⟩

theorem isUnit_of_not_mem (hv : v.Integers R) {r : R} (h : r ∉ mI hv) : IsUnit r :=
  hv.isUnit_of_one' ((v_eq_one_iff hv r).2 h)

theorem mI_isMaximal (hv : v.Integers R) : (mI hv).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨by simp [mem_mI], fun J x hle hx hxJ => ?_⟩
  obtain ⟨u, rfl⟩ := isUnit_of_not_mem hv hx
  have : (↑u⁻¹ : R) * u ∈ J := J.mul_mem_left _ hxJ
  simpa using this

theorem isDomain (hv : v.Integers R) : IsDomain R := by
  have : Nontrivial R := ⟨0, 1, fun h => by
    have := congrArg (fun r => v (algebraMap R C r)) h
    simp at this⟩
  exact hv.hom_inj.isDomain (algebraMap R C)

abbrev res (hv : v.Integers R) : R →+* R ⧸ mI hv := Ideal.Quotient.mk (mI hv)

theorem res_eq_zero (hv : v.Integers R) (r : R) : res hv r = 0 ↔ v (algebraMap R C r) < 1 :=
  Ideal.Quotient.eq_zero_iff_mem

theorem res_ne_zero (hv : v.Integers R) (r : R) : res hv r ≠ 0 ↔ v (algebraMap R C r) = 1 := by
  rw [Ne, res_eq_zero, v_eq_one_iff hv, mem_mI]

instance instField (hv : v.Integers R) : Field (R ⧸ mI hv) :=
  haveI := mI_isMaximal hv
  Ideal.Quotient.field _

theorem charP (p : ℕ) [hp : Fact p.Prime] (hv : v.Integers R)
    (hpv : v (algebraMap R C (p : R)) < 1) : CharP (R ⧸ mI hv) p := by
  have h0 : ((p : R ⧸ mI hv)) = 0 := by
    rw [← map_natCast (res hv), res_eq_zero]; exact hpv
  exact (CharP.charP_iff_prime_eq_zero hp.out).2 h0

theorem idem_eq_zero (hv : v.Integers R) {n : Type} [Fintype n] [DecidableEq n]
    (e : Matrix n n R) (he : e * e = e) (hm : ∀ a b, e a b ∈ mI hv) : e = 0 := by
  have hmap : e.map (res hv) = 0 := by
    ext a b; simpa [Ideal.Quotient.eq_zero_iff_mem] using hm a b
  have hdet : IsUnit (1 - e).det := by
    apply isUnit_of_not_mem hv
    intro h
    have h1 : res hv (1 - e).det = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h
    rw [RingHom.map_det, map_sub, map_one, RingHom.mapMatrix_apply, hmap, sub_zero,
      Matrix.det_one] at h1
    exact one_ne_zero h1
  have hu : IsUnit (1 - e) := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  exact (hu.mul_left_eq_zero).1 this

theorem root_eq (hv : v.Integers R) {n : ℕ} (hn : (n : R) ∉ mI hv) {x y : R} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (hxy : x - y ∈ mI hv) : x = y := by
  have := isDomain hv
  have hgeom := (Commute.all x y).geom_sum₂_mul n
  rw [hx, hy, sub_self] at hgeom
  rcases mul_eq_zero.1 hgeom with h | h
  · exfalso
    have hres : res hv (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = (n : R ⧸ mI hv) * res hv x ^ (n - 1) := by
      have hxy' : res hv x = res hv y := by
        rw [← sub_eq_zero, ← map_sub]; exact Ideal.Quotient.eq_zero_iff_mem.2 hxy
      rw [map_sum]
      simp only [map_mul, map_pow, ← hxy']
      rw [Finset.sum_congr rfl (g := fun _ => res hv x ^ (n - 1)), Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      intro i hi
      rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega
    have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hx0 : res hv x ≠ 0 := by
      intro h0; have := congrArg (res hv) hx; rw [map_pow, h0, zero_pow hn0, map_one] at this
      exact zero_ne_one this
    have hnn : (n : R ⧸ mI hv) ≠ 0 := by
      rw [← map_natCast (res hv)]; exact fun h0 => hn (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    rw [h, map_zero] at hres
    exact mul_ne_zero hnn (pow_ne_zero _ hx0) hres.symm
  · exact sub_eq_zero.1 h

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField

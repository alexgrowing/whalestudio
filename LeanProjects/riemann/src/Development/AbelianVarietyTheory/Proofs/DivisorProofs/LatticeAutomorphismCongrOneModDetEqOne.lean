import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem det_eq_one_of_congMod (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : X ≃+ X) (m : ℕ)
    (hm : 3 ≤ m) (hk : ∀ x, CongMod m (k x) x) :
    LinearMap.det (k.toIntLinearEquiv : X →ₗ[ℤ] X) = 1 := by
  set f : X ≃ₗ[ℤ] X := k.toIntLinearEquiv
  have hu : IsUnit (LinearMap.det (f : X →ₗ[ℤ] X)) := LinearEquiv.isUnit_det' f
  let b := Module.Free.chooseBasis ℤ X
  set M := LinearMap.toMatrix b b (f : X →ₗ[ℤ] X) with hM
  have hdet : M.det = LinearMap.det (f : X →ₗ[ℤ] X) := LinearMap.det_toMatrix b _
  have hmap : (Int.castRingHom (ZMod m)).mapMatrix M = 1 := by
    ext i j
    obtain ⟨w, hw⟩ := hk (b j)
    have hfb : (f : X →ₗ[ℤ] X) (b j) = k (b j) := rfl
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hM, LinearMap.toMatrix_apply, hfb, hw, map_add, map_nsmul,
      Finsupp.add_apply, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, Matrix.one_apply]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hz : ((LinearMap.det (f : X →ₗ[ℤ] X) : ℤ) : ZMod m) = 1 := by
    rw [← hdet]
    have := RingHom.map_det (Int.castRingHom (ZMod m)) M
    rw [hmap, Matrix.det_one] at this
    simpa using this
  rcases Int.isUnit_iff.mp hu with h | h
  · exact h
  · exfalso
    rw [h] at hz
    have h2 : ((2 : ℕ) : ZMod m) = 0 := by
      have e : ((2 : ℕ) : ZMod m) = 1 - ((-1 : ℤ) : ZMod m) := by push_cast; ring
      rw [e, hz, sub_self]
    have hd := (ZMod.natCast_eq_zero_iff 2 m).mp h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

end GlobalTheory.Poinc

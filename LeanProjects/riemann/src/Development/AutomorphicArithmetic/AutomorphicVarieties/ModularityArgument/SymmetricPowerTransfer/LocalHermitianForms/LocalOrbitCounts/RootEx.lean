import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Loc.rootEx : UpperTheory.V.Z.Sym.Loc.RootEx := by
  intro O K _ _ _ _ _ Δ τ hL τ₀ e hτ hm
  subst hτ
  have h2 : IsUnit (2 : O) := hL.two
  have eZ : ((e : ℤ)) * (e : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have he : ((e : ℤ) : O) * ((e : ℤ) : O) = 1 := by
    exact_mod_cast congrArg (fun n : ℤ => (n : O)) eZ
  have eK : ((e : ℤ) : K) * ((e : ℤ) : K) = 1 := by
    exact_mod_cast congrArg (fun n : ℤ => (n : K)) eZ
  obtain ⟨s, hs, hs2⟩ := sqrtO O K Δ hL (((e : ℤ) : O) * (τ₀ + 2 * ((e : ℤ) : O))) 2 h2 (by
    have hrw : ((e : ℤ) : O) * (τ₀ + 2 * ((e : ℤ) : O)) - 2 ^ 2
        = ((e : ℤ) : O) * (τ₀ - 2 * ((e : ℤ) : O)) := by
      linear_combination (4 : O) * he
    rw [hrw]
    exact Ideal.mul_mem_left _ _ hm)
  have hsu : IsUnit s := by
    by_contra hn
    have hsm : s ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal s).2 ((mem_nonunits_iff).2 hn)
    have h2m : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ hsm hs2
      rwa [sub_sub_cancel] at this
    exact ((mem_nonunits_iff).1 ((IsLocalRing.mem_maximalIdeal _).1 h2m)) h2
  set y : O := ((hsu.unit⁻¹ : Oˣ) : O) with hydef
  have hy : s * y = 1 := hsu.mul_val_inv
  have key : (τ₀ + 2 * ((e : ℤ) : O)) * y ^ 2 = ((e : ℤ) : O) := by
    linear_combination (-(τ₀ + 2 * ((e : ℤ) : O)) * y ^ 2) * he
      + (-((e : ℤ) : O) * y ^ 2) * hs + ((e : ℤ) : O) * (s * y + 1) * hy
  have kK : ((algebraMap O K) τ₀ + 2 * ((e : ℤ) : K)) * ((algebraMap O K) y) ^ 2
      = ((e : ℤ) : K) := by
    have := congrArg (algebraMap O K) key
    simpa [map_mul, map_add, map_pow, map_intCast, map_ofNat] using this
  refine ⟨((e : ℤ) : O) * y, y, Units.isUnit _, ?_, ?_⟩
  · rw [sq]
    ext
    · simp [map_mul, map_intCast]
      linear_combination ((algebraMap O K) y) ^ 2 * eK
    · simp [map_mul, map_intCast]
      linear_combination kK
  · rw [QuadraticAlgebra.norm_def]
    simp only [map_mul, map_intCast]
    linear_combination ((e : ℤ) : K) * kK + (1 - ((algebraMap O K) y) ^ 2) * eK

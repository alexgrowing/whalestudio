import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Average

namespace KStar.Ram

open DirichletCharacter

section PrimePower

variable {l v : ℕ} [hl : Fact l.Prime]

private instance bounds_neZero : NeZero (l ^ v) := ⟨pow_ne_zero _ hl.out.ne_zero⟩

private def boundsSub (m d : ℕ) [NeZero m] : Subgroup (DirichletCharacter ℂ m) where
  carrier := {θ | θ.conductor ∣ d}
  mul_mem' {a b} ha hb := (conductor_mul_dvd_lcm_conductor a b).trans (Nat.lcm_dvd ha hb)
  one_mem' := by simp [conductor_one]
  inv_mem' {a} ha := by simpa [conductor_inv] using ha

end PrimePower

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

end KStar.Ram

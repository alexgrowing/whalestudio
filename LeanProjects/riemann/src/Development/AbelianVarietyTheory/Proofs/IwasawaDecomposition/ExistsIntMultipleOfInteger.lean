import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory

theorem algInt_dvd_nonzero_intCast : ∀ (E : Type) [Field E] [NumberField E] (u : 𝓞 E), u ≠ 0 → ∃ c : ℤ, c ≠ 0 ∧ u ∣ (c : 𝓞 E) := by
  intro E _ _ u hu
  refine ⟨Algebra.intNorm ℤ (𝓞 E) u, Algebra.intNorm_ne_zero.2 hu, ?_⟩
  have := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 E) u
  simpa using this

end GlobalTheory

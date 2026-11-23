import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

def HasseNormSt : Prop := (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2)

namespace HasseNormSt

open scoped TensorProduct

theorem of_isSquare {F : Type*} [Field F] [CharZero F] {δ : F} (h0 : δ ≠ 0) (hδ : _root_.IsSquare δ) (x : F) :
    ∃ a b : F, x = a ^ 2 - δ * b ^ 2 := by
  obtain ⟨r, rfl⟩ := hδ
  have hr : r ≠ 0 := fun hr => h0 (by rw [hr, mul_zero])
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  refine ⟨(x + 1) / 2, (x - 1) / (2 * r), ?_⟩
  field_simp
  ring

end HasseNormSt

end GlobalTheory.Published

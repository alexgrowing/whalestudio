import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.LatOfMult

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → (∀ a : 𝓞 K, MulStable Λ (ι a)) ∧ MulStable Λ (ι δ) ∧ (ι δ).im ≠ 0 ∧ IsIntegral ℤ δ := by
  intro K _ _ d δ ι 𝔞 Λ hd hδ hL
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice ↔ ∃ x ∈ (𝔞 : Set K), ι x = z := by
    intro z
    have := congrArg (fun S : Set ℂ => z ∈ S) hL
    simpa using this
  have hstab : ∀ a : 𝓞 K, MulStable Λ (ι a) := by
    intro a ω hω
    obtain ⟨x, hx, rfl⟩ := (hmem ω).1 hω
    refine (hmem _).2 ⟨(a : K) * x, ?_, by simp⟩
    have h1 : a • x ∈ (𝔞 : Submodule (𝓞 K) K) := Submodule.smul_mem _ a hx
    rwa [Algebra.smul_def] at h1
  have hint : IsIntegral ℤ δ := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hδ]
  refine ⟨hstab, ?_, ?_, hint⟩
  · exact hstab ⟨δ, hint⟩
  · intro him
    have h2 : (ι δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
    have h3 := congrArg Complex.re h2
    simp [pow_two, Complex.mul_re, him] at h3
    have : (0:ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg (ι δ).re]

end GlobalTheory.LatOfMult

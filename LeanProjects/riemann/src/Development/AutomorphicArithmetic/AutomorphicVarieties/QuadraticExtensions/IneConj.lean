import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.ineConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (v : G F Ω), (∀ (B : ValuationSubring Ω) (g : G F Ω), g ∈ Ine (F := F) (v • B) → v⁻¹ * g * v ∈ Ine (F := F) B) ∧
      (∀ (B : ValuationSubring Ω) (N : ℕ), (v • B).valuation (N : Ω) < 1 ↔ B.valuation (N : Ω) < 1) ∧ ∀ (N : ℕ), ∀ s ∈ ineOff F Ω N, v⁻¹ * s * v ∈ ineOff F Ω N := by
  intro F Ω _ _ _ _ _ v
  have hlt : ∀ (A : ValuationSubring Ω) (y : Ω), y ≠ 0 → (A.valuation y < 1 ↔ y⁻¹ ∉ A) := by
    intro A y hy
    rw [← A.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hy), inv_inv]
  have hL : ∀ (w : G F Ω) (B : ValuationSubring Ω) (x : Ω), (w • B).valuation x < 1 ↔ B.valuation (w⁻¹ • x) < 1 := by
    intro w B x
    by_cases hx : x = 0
    · subst hx
      simp
    have hx' : w⁻¹ • x ≠ 0 := by simpa using hx
    rw [hlt _ _ hx, hlt _ _ hx', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'']
  have p1 : ∀ (B : ValuationSubring Ω) (g : G F Ω), g ∈ Ine (F := F) (v • B) → v⁻¹ * g * v ∈ Ine (F := F) B := by
    intro B g hg
    obtain ⟨hd, hi⟩ := hg
    refine ⟨?_, ?_⟩
    · have hd' : g • (v • B) = v • B := hd
      show (v⁻¹ * g * v) • B = B
      rw [mul_smul, mul_smul, hd', inv_smul_smul]
    · intro x hx
      have hvx : (v • B).valuation (v x) ≤ 1 := by
        rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
          ← ValuationSubring.valuation_le_one_iff]
        simpa [AlgEquiv.smul_def] using hx
      have h2 := hi (v x) hvx
      rw [hL] at h2
      convert h2 using 2
      simp [AlgEquiv.smul_def, map_sub, AlgEquiv.mul_apply]
  have p2 : ∀ (B : ValuationSubring Ω) (N : ℕ), (v • B).valuation (N : Ω) < 1 ↔ B.valuation (N : Ω) < 1 := by
    intro B N
    rw [hL]
    simp [AlgEquiv.smul_def]
  refine ⟨p1, p2, ?_⟩
  rintro N s ⟨A, hA, hs⟩
  have hA' : v • (v⁻¹ • A) = A := smul_inv_smul v A
  refine ⟨v⁻¹ • A, ?_, ?_⟩
  · rw [← p2, hA']
    exact hA
  · apply p1
    rw [hA']
    exact hs

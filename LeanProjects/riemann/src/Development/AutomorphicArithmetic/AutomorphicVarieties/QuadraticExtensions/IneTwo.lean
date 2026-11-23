import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem not_lt_one_of_coprime {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p m : ℕ} (h : p.Coprime m)
    (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (m : Ω) < 1 := by
  intro hm
  have hz : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z => A.valuation_le_one ⟨(z : Ω), intCast_mem A z⟩
  have h1 : ((p : ℤ) * Nat.gcdA p m + (m : ℤ) * Nat.gcdB p m : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one h]
    rfl
  have hcast : (p : Ω) * (Nat.gcdA p m : Ω) + (m : Ω) * (Nat.gcdB p m : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) h1
    push_cast at this
    exact this
  have ha : A.valuation ((p : Ω) * (Nat.gcdA p m : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hz _)) hp
  have hb : A.valuation ((m : Ω) * (Nat.gcdB p m : Ω)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hz _)) hm
  have := lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ha hb)
  rw [hcast, map_one] at this
  exact lt_irrefl _ this

theorem UpperTheory.V.Two.ineTwo :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (p : ℕ) (A : ValuationSubring Ω), p.Coprime (2 * M.m) → A.valuation (p : Ω) < 1 → Ine (F := ℚ) A ≤ cycU 2 (abU Ω (withI M)) := by
  intro Ω _ _ _ M p A hcop hp
  have h2 : p.Coprime 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 M.m) hcop
  have hM : p.Coprime M.m := Nat.Coprime.coprime_dvd_right (dvd_mul_left M.m 2) hcop
  have hW : p.Coprime (withI M).m := by
    show p.Coprime (M.m * max 4 1)
    exact Nat.Coprime.mul_right hM (by simpa using Nat.Coprime.pow_right 2 h2)
  intro g hg
  refine ⟨?_, ?_⟩
  · have := ineChar Ω (withI M).m A (not_lt_one_of_coprime A hW hp) hg
    rw [MonoidHom.mem_ker] at this
    show galChar Ω (withI M).m g ∈ (withI M).H
    rw [this]
    exact Subgroup.one_mem _
  · exact (places ℚ Ω 2 A).2.2.2 (not_lt_one_of_coprime A h2 hp) hg

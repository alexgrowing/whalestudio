import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.SupIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.DecIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.OrbIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.AbBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.LevChar

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.orbTwo :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : AbF) (p c : ℕ), p.Prime → (p % 8 = 3 ∧ c = 2 ∨ p % 16 = 7 ∧ c = 4) → OrbLe (cycU 2 (abU Ω (withI M))) p (c * M.deg) := by
  intro Ω _ _ _ M p c hp hc
  classical
  obtain ⟨hsupAb, hdeg, hmem, hcyc⟩ := abBasic Ω
  have hK4 : (cycZ ℚ Ω 2).ker ≤ (galChar Ω 4).ker := (levChar Ω 2 2 ⊤).2
  have hV : cycU 2 (abU Ω (withI M)) = abU Ω M ⊓ (cycZ ℚ Ω 2).ker := by
    show abU Ω (M.sup (AbF.cyc 4)) ⊓ (cycZ ℚ Ω 2).ker = _
    rw [hsupAb, hcyc 4, inf_assoc, inf_eq_right.mpr hK4]
  haveI hWn : (abU Ω M).Normal := by
    haveI : NeZero M.m := ⟨M.pos.ne'⟩
    constructor
    intro g hg h
    rw [hmem M M.m dvd_rfl] at hg ⊢
    have hconj : galChar Ω M.m (h * g * h⁻¹) = galChar Ω M.m g := by
      rw [map_mul, map_mul, map_inv, mul_comm (galChar Ω M.m h), mul_inv_cancel_right]
    rw [hconj]
    exact hg
  rw [hV]
  by_cases hex : ∃ A₀ : ValuationSubring Ω, A₀.valuation (p : Ω) < 1
  · obtain ⟨A₀, hA₀⟩ := hex
    obtain ⟨hKD0, hKDle⟩ := decIndex Ω p c A₀ hp hc hA₀
    have hi : (abU Ω M).index = M.deg := (hdeg M).1
    have hW0 : (abU Ω M).index ≠ 0 := hi ▸ (hdeg M).2.1
    obtain ⟨hne, hle⟩ := supIndex (G ℚ Ω) (cycZ ℚ Ω 2).ker (abU Ω M) (Dec A₀) hW0 hKD0
    obtain ⟨T, hT, h1, h2⟩ := orbIndex Ω p (abU Ω M ⊓ (cycZ ℚ Ω 2).ker) A₀ hp hA₀ hne
    refine ⟨T, hT.trans ?_, h1, h2⟩
    calc _ ≤ (abU Ω M).index * ((cycZ ℚ Ω 2).ker ⊔ Dec A₀).index := hle
      _ ≤ M.deg * c := by rw [hi]; exact Nat.mul_le_mul_left _ hKDle
      _ = c * M.deg := Nat.mul_comm _ _
  · push_neg at hex
    exact ⟨∅, by simp, by simp, fun A hA => absurd hA (not_lt.mpr (hex A))⟩

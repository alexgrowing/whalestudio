import Formalism.LocalToGlobal.GlobalTheory.GL2.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.TopDensityNGeSixteen
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes NumberField

theorem NE_pos (D : D7) : 0 < NE D :=
  Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by have := D.host.qd_big.1; omega))
    (by have := D.host.qd_big.2; omega)

theorem splits_of_modEq (D : D7) (hC : CycSplit) {p : ℕ} (hp : p.Prime) (h1 : p ≡ 1 [MOD NE D]) :
    SplitsCompletely D p := by
  letI : Algebra D.host.E (CyclotomicField (NE D) ℚ) := D.host.cycEmb.toRingHom.toAlgebra
  exact hC (NE D) p D.host.E (NE_pos D) hp h1

theorem modEq_of_normOneMod (D : D7) {M g : ℕ} (h : NormOneMod D M g) : g ≡ 1 [MOD M] := by
  obtain ⟨π, ρ, -, -, h1, h2⟩ := h
  have ht : ((g : D.host.E) - 1) = (M : D.host.E) * ((ρ : D.host.E) + D.host.conj (ρ : D.host.E) +
      (M : D.host.E) * (ρ : D.host.E) * D.host.conj (ρ : D.host.E)) := by
    have hπ : (π : D.host.E) = 1 + M * ρ := by linear_combination h1
    rw [← h2, hπ, map_add, map_one, map_mul, map_natCast]
    ring
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have hg : (g : D.host.E) = 1 := by
      have h0 : ((g : D.host.E) - 1) = 0 := by rw [ht]; simp
      linear_combination h0
    have hg1 : g = 1 := by exact_mod_cast hg
    subst hg1
    rfl
  ·
    have hρ : IsIntegral ℤ (ρ : D.host.E) := NumberField.RingOfIntegers.isIntegral_coe ρ
    have hρc : IsIntegral ℤ (D.host.conj (ρ : D.host.E)) := hρ.map D.host.conj
    have hint : IsIntegral ℤ ((ρ : D.host.E) + D.host.conj (ρ : D.host.E) +
        (M : D.host.E) * (ρ : D.host.E) * D.host.conj (ρ : D.host.E)) := by
      have hMρ : IsIntegral ℤ ((M : D.host.E) * (ρ : D.host.E)) := by
        rw [← nsmul_eq_mul]
        exact hρ.nsmul M
      exact (hρ.add hρc).add (hMρ.mul hρc)
    have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have hME : (M : D.host.E) ≠ 0 := by exact_mod_cast hM.ne'
    have hq : algebraMap ℚ D.host.E (((g : ℚ) - 1) / M) = (ρ : D.host.E) + D.host.conj (ρ : D.host.E) +
        (M : D.host.E) * (ρ : D.host.E) * D.host.conj (ρ : D.host.E) := by
      rw [map_div₀, map_sub, map_natCast, map_one, map_natCast, ht]
      field_simp
    rw [← hq, isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective] at hint
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    rw [algebraMap_int_eq, eq_intCast] at hn
    have hgq : ((g : ℚ) - 1) = M * n := by
      rw [hn]
      field_simp
    rw [Nat.modEq_iff_dvd]
    refine ⟨-n, ?_⟩
    have hz : ((1 : ℤ) - g : ℚ) = ((M * -n : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast hz

theorem split_clause (D : D7) (hC : CycSplit) :
    ∀ g : ℕ, g.Prime → NormOneMod D (NE D) g → g ≡ 1 [MOD NE D] ∧ SplitsCompletely D g :=
  fun g hg h => ⟨modEq_of_normOneMod D h, splits_of_modEq D hC hg (modEq_of_normOneMod D h)⟩

end Formalism.L2.GlobalTheoryTheory.FiltrationCocycleLiftCriterion

end

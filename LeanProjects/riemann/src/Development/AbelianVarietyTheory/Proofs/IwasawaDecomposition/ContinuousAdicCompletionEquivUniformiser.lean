import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuousStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnifMap

theorem unif_to_unif : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) (i : v.adicCompletion F ≃+* w.adicCompletion E), Continuous i →
    ∀ ϖ : v.adicCompletion F, Valued.v ϖ = WithZero.exp (-1 : ℤ) → Valued.v (i ϖ) = WithZero.exp (-1 : ℤ) := by
  intro F E _ _ _ _ v w i hi ϖ hϖ
  have hle := GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv F E v w i hi
  have key : ∀ x : WithZero (Multiplicative ℤ), x ≠ 0 → x < 1 → x ≤ WithZero.exp (-1 : ℤ) := by
    intro x hx h1
    rw [← WithZero.exp_log hx] at h1 ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [WithZero.exp_le_exp]; omega
  have hlt : ∀ y, Valued.v (i y) < 1 ↔ Valued.v y < 1 := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · have hiy : i y ≠ 0 := by simpa using hy
      have e1 := (Valued.v (R := w.adicCompletion E)).one_lt_val_iff (inv_ne_zero hiy)
      have e2 := (Valued.v (R := v.adicCompletion F)).one_lt_val_iff (inv_ne_zero hy)
      rw [inv_inv] at e1 e2
      rw [← e1, ← e2, ← not_le, ← not_le, ← map_inv₀ i, hle]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hiϖ0 : i ϖ ≠ 0 := by simpa using hϖ0
  have hϖ1 : Valued.v ϖ < 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hup : Valued.v (i ϖ) < 1 := (hlt ϖ).2 hϖ1
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  set z : w.adicCompletion E := (π : w.adicCompletion E)
  have hz : Valued.v z = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  set y := i.symm z
  have hy1 : Valued.v y < 1 := by
    rw [← hlt, RingEquiv.apply_symm_apply, hz, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy1
    have : z = 0 := by simpa [y] using h
    rw [this, map_zero] at hz; exact WithZero.exp_ne_zero hz.symm
  have hdiv : Valued.v (y / ϖ) ≤ 1 := by
    rw [map_div₀, hϖ, div_le_one₀ (by simp)]
    exact key _ (by simpa using hy0) hy1
  have h2 := (hle _).2 hdiv
  rw [map_div₀, map_div₀, RingEquiv.apply_symm_apply, hz] at h2
  have hlow : WithZero.exp (-1 : ℤ) ≤ Valued.v (i ϖ) := by
    rwa [div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hiϖ0))] at h2
  exact le_antisymm (key _ (by simpa using hiϖ0) hup) hlow

end GlobalTheory.UnifMap

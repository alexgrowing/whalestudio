import Mathlib
import Formalism.PeriodIntegrals.DiffGenLoc

noncomputable section

namespace PI.DiffGenLoc.UnitaryGroupMassFormula

open NumberField IsDedekindDomain WithZero

theorem val_alg {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := by
  first
    | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)).trans
        (HeightOneSpectrum.valuation_of_algebraMap v x)
    | (rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]; rfl)
    | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
    | (rw [HeightOneSpectrum.adicCompletion.algebraMap_eq_coe, HeightOneSpectrum.valuedAdicCompletion_eq_valuation,
        HeightOneSpectrum.valuation_of_algebraMap])

theorem diffExists_main {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : DiffExists v := by
  classical
  have hI : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hne : ∀ x : 𝓞 F, x ≠ 0 → v.intValuation x ≠ 0 := fun x hx => by
    first
      | exact v.intValuation_ne_zero x hx
      | exact v.intValuation_ne_zero' x hx
      | exact (map_ne_zero _).2 hx
      | simpa using hx
  let f : 𝓞 F → ℕ := fun x =>
    if hx : x = 0 then 0 else (-(Multiplicative.toAdd (WithZero.unzero (hne x hx)))).toNat
  have hfdef : ∀ z (hz : z ≠ 0), f z = (-(Multiplicative.toAdd (WithZero.unzero (hne z hz)))).toNat :=
    fun z hz => dif_neg hz
  have key : ∀ z : 𝓞 F, ∀ hz : z ≠ 0,
      v.intValuation z = ((Multiplicative.ofAdd (-(f z : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro z hz
    have hu : ((WithZero.unzero (hne z hz) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = v.intValuation z :=
      WithZero.coe_unzero _
    have hle : Multiplicative.toAdd (WithZero.unzero (hne z hz)) ≤ 0 := by
      have h1 : ((WithZero.unzero (hne z hz) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
          ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
        rw [hu, WithZero.coe_one]
        exact v.intValuation_le_one z
      rw [WithZero.coe_le_coe] at h1
      have h2 := Multiplicative.toAdd_le.2 h1
      simpa using h2
    rw [hfdef z hz, Int.toNat_of_nonneg (by linarith), neg_neg, ofAdd_toAdd, hu]
  have hP : ∃ n, ∃ x ∈ differentIdeal ℤ (𝓞 F), x ≠ 0 ∧ f x = n := ⟨_, y, hyI, hy0, rfl⟩
  obtain ⟨x₀, hx₀I, hx₀0, hfx₀⟩ := Nat.find_spec hP
  refine ⟨algebraMap F (Fv F v) (x₀ : F), ?_, ?_, x₀, hx₀I, rfl⟩
  · intro h
    apply hx₀0
    have h1 : ((x₀ : F)) = 0 := (algebraMap F (Fv F v)).injective (h.trans (map_zero _).symm)
    exact_mod_cast h1
  · intro x hxI
    rw [val_alg, val_alg]
    by_cases hx : x = 0
    · simp [hx]
    have hmin : Nat.find hP ≤ f x := Nat.find_min' hP ⟨x, hxI, hx, rfl⟩
    rw [key x hx, key x₀ hx₀0, WithZero.coe_le_coe, Multiplicative.ofAdd_le, neg_le_neg_iff, Nat.cast_le, hfx₀]
    exact hmin

end PI.DiffGenLoc.UnitaryGroupMassFormula

import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMinpolyMemAdicCompletionIntegers
open scoped TensorProduct Classical
open Polynomial

namespace GlobalTheory.IntegralDescent

theorem not_dvd_den_coeff_minpoly (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (ℓ : ℕ) [Fact ℓ.Prime] (w : E) (hw : IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w)) (i : ℕ) :
    ¬ ℓ ∣ ((minpoly ℚ w).coeff i).den := by
  obtain ⟨p, hpm, hp⟩ := hw
  have hzi : IsIntegral ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) := IsIntegral.of_finite _ _
  have hdvd : minpoly ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) ∣ p.map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
    apply minpoly.dvd
    rw [aeval_def, eval₂_map]
    exact hp
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ_[ℓ] hpm hdvd
  rw [(minpoly.monic hzi).leadingCoeff, C_1, mul_one, GlobalTheory.DescCoeff.minpoly_one_tmul_eq] at hg
  have hc := congrArg (fun q => q.coeff i) hg
  simp only [coeff_map] at hc
  have hn : ‖(((minpoly ℚ w).coeff i : ℚ) : ℚ_[ℓ])‖ ≤ 1 := by
    rw [← eq_ratCast (algebraMap ℚ ℚ_[ℓ]), ← hc]
    exact (g.coeff i).2
  intro hd
  have hu := PadicInt.isUnit_den _ hn
  exact PadicInt.irreducible_p.not_isUnit
    (isUnit_of_dvd_unit (Nat.cast_dvd_cast (α := ℤ_[ℓ]) hd) hu)

theorem exists_not_dvd_isIntegral_mul : ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] (ℓ : ℕ) [Fact ℓ.Prime] (w : E), IsIntegral ℤ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] w) → ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * w) := by
  intro E _ _ _ ℓ hℓ w hw
  set f := minpoly ℚ w with hf
  have hfm : f.Monic := minpoly.monic (IsIntegral.of_finite ℚ w)
  set d : ℕ := ∏ i ∈ Finset.range f.natDegree, (f.coeff i).den with hd
  refine ⟨d, ?_, ?_⟩
  · intro h
    obtain ⟨i, -, hi⟩ := (hℓ.out.prime.dvd_finsetProd_iff _).mp h
    exact not_dvd_den_coeff_minpoly E ℓ w hw i hi
  · have hroot : aeval ((d : E) * w) (f.scaleRoots (d : ℚ)) = 0 := by
      have := scaleRoots_aeval_eq_zero (r := (d : ℚ)) (minpoly.aeval ℚ w)
      rwa [map_natCast] at this
    have hlift : f.scaleRoots (d : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
      rw [lifts_iff_coeff_lifts]
      intro i
      rw [coeff_scaleRoots]
      rcases lt_trichotomy i f.natDegree with hi | hi | hi
      · obtain ⟨c, hc⟩ : (f.coeff i).den ∣ d :=
          Finset.dvd_prod_of_mem (fun j => (f.coeff j).den) (Finset.mem_range.mpr hi)
        obtain ⟨k, hk⟩ : ∃ k, f.natDegree - i = k + 1 := ⟨f.natDegree - i - 1, by omega⟩
        refine ⟨(f.coeff i).num * c * (d : ℤ) ^ k, ?_⟩
        rw [hk, pow_succ]
        have h1 : (d : ℚ) = ((f.coeff i).den : ℚ) * c := by exact_mod_cast hc
        have h2 : f.coeff i * ((f.coeff i).den : ℚ) = (f.coeff i).num := Rat.mul_den_eq_num _
        simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
        rw [← h2]
        linear_combination (-(f.coeff i) * (d : ℚ) ^ k) * h1
      · subst hi
        exact ⟨1, by simp [hfm.coeff_natDegree]⟩
      · exact ⟨0, by simp [coeff_eq_zero_of_natDegree_lt hi]⟩
    obtain ⟨q, hq, -, hqm⟩ :=
      lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff _).mpr hfm)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ, hq]
    exact hroot

end GlobalTheory.IntegralDescent

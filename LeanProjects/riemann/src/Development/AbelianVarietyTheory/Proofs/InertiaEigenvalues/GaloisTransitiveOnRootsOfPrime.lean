import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem galois_transitive_on_roots_of_prime (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K))
    (hπ : Prime π) (n : ℕ) (y z : Om l) (hy : y ^ n = ((π : ↥K.1) : Om l))
    (hz : z ^ n = ((π : ↥K.1) : Om l)) (hn : 0 < n) : ∃ g : ↥(GK K), (g : GQ l) y = z := by
  classical

  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : IsFractionRing ↥(OL K) ↥K.1 :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥K.1
  have : IsIntegrallyClosed ↥(OL K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension ℚ_[l]
  have hn0 : n ≠ 0 := hn.ne'
  have hmon : (Polynomial.X ^ n - Polynomial.C π).Monic := Polynomial.monic_X_pow_sub_C π hn0

  have hirr : Irreducible (Polynomial.X ^ n - Polynomial.C π) := by
    refine Polynomial.irreducible_of_eisenstein_criterion
      ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ) ?_ ?_ ?_ ?_ hmon.isPrimitive
    · rw [hmon.leadingCoeff]
      intro h
      exact hπ.not_isUnit (Ideal.span_singleton_eq_top.1 ((Ideal.eq_top_iff_one _).2 h))
    · intro m hm
      rw [Polynomial.degree_X_pow_sub_C hn π, Nat.cast_lt] at hm
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hm.ne]
      split_ifs
      · exact Ideal.sub_mem _ (Ideal.zero_mem _) (Ideal.mem_span_singleton_self π)
      · simp
    · rw [Polynomial.degree_X_pow_sub_C hn π]
      exact_mod_cast hn
    · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hn0.symm,
        if_pos rfl, zero_sub, Ideal.span_singleton_pow, Ideal.neg_mem_iff, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      apply hπ.not_isUnit
      have h1 : π * 1 = π * (π * c) := by
        rw [mul_one, ← mul_assoc, ← pow_two]
        exact hc
      exact isUnit_of_dvd_one ⟨c, mul_left_cancel₀ hπ.ne_zero h1⟩

  have hirrF : Irreducible (Polynomial.X ^ n - Polynomial.C ((π : ↥K.1))) := by
    have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ↥K.1)).1 hirr
    rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] at h
  have hmin : ∀ w : Om l, w ^ n = ((π : ↥K.1) : Om l) →
      minpoly (↥K.1) w = Polynomial.X ^ n - Polynomial.C ((π : ↥K.1)) := by
    intro w hw
    refine (minpoly.eq_of_irreducible_of_monic hirrF ?_ (Polynomial.monic_X_pow_sub_C _ hn0)).symm
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      IntermediateField.algebraMap_apply, hw, sub_self]

  have : Normal (↥K.1) (Om l) := Normal.tower_top_of_normal ℚ_[l] (↥K.1) (Om l)
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ↥K.1) (E := Om l)).1
    ((hmin z hz).trans (hmin y hy).symm)
  refine ⟨⟨σ.restrictScalars ℚ_[l], ?_⟩, hσ⟩
  show σ.restrictScalars ℚ_[l] ∈ IntermediateField.fixingSubgroup K.1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact σ.commutes ⟨x, hx⟩

end GlobalTheory

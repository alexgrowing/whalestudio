import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.Development

open NumberField

noncomputable section

namespace PI.UG.W

theorem hStd_apply (E : Type) [Field E] [StarRing E] (n : ℕ) (x y : Sp E n) :
    hStd E n x y = ∑ i, star (x i) * y i := rfl

theorem hStd_isSymm (E : Type) [Field E] [StarRing E] (n : ℕ) : (hStd E n).IsSymm := by
  refine LinearMap.isSymm_def.mpr fun x y => ?_
  rw [hStd_apply, hStd_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply, star_mul, star_star, mul_comm]

theorem star_mem_range (E : Type) [Field E] [NumberField E] [StarRing E] (r : 𝓞 E) :
    star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
  exact ⟨⟨star (algebraMap (𝓞 E) E r), (RingOfIntegers.isIntegral_coe r).map (starRingEnd E).toIntAlgHom⟩, rfl⟩

def eStd (E : Type) [Field E] (n : ℕ) (i : Fin n) : Sp E n := Pi.single i 1

theorem hStd_eStd (E : Type) [Field E] [StarRing E] (n : ℕ) (i j : Fin n) :
    hStd E n (eStd E n i) (eStd E n j) = if i = j then 1 else 0 := by
  rw [hStd_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [eStd, hk]) (by simp)]
    simp [eStd]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i
    · subst hk
      simp [eStd, Ne.symm h]
    · simp [eStd, Pi.single_apply, hk]

theorem stdLat_eq_span (E : Type) [Field E] [NumberField E] (n : ℕ) :
    stdLat E n = Submodule.span (𝓞 E) (Set.range (eStd E n)) := by
  apply le_antisymm
  · intro x hx
    have h' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = x i := fun i =>
      Submodule.mem_one.mp ((Submodule.mem_pi.mp hx) i (Set.mem_univ i))
    choose a ha using h'
    have hx' : x = ∑ i, a i • eStd E n i := by
      ext k
      simp [eStd, Pi.single_apply, Finset.sum_apply, ← ha, Algebra.smul_def]
    rw [hx']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.mem_pi.mpr fun k _ => Submodule.mem_one.mpr ?_
    by_cases h : k = i
    · subst h
      exact ⟨1, by simp [eStd]⟩
    · exact ⟨0, by simp [eStd, h]⟩

end PI.UG.W

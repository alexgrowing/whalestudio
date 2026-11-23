import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.HeightOneIffDimOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthEqOfSurjOfKerEq

namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

theorem length_quotient_kernel (a b : A) :
    length (A ⧸ Ideal.span {a}) (LinearMap.ker (LinearMap.lsmul (A ⧸ Ideal.span {a})
        (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) := by
  rw [length_quot_restrict a]
  have h : (LinearMap.ker (LinearMap.lsmul (A ⧸ Ideal.span {a})
        (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))).restrictScalars A =
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) := by
    ext x
    simp [Algebra.smul_def]
  rw [← h]
  rfl

theorem length_quotient_cokernel (a b : A) :
    length (A ⧸ Ideal.span {a}) ((A ⧸ Ideal.span {a}) ⧸ LinearMap.range (LinearMap.lsmul
        (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b))) =
      length A (A ⧸ Ideal.span {a, b}) := by
  rw [length_quot_restrict a]
  set N := LinearMap.range (LinearMap.lsmul
        (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk (Ideal.span {a}) b)) with hN
  let f : A →ₗ[A] ((A ⧸ Ideal.span {a}) ⧸ N) :=
    (N.mkQ.restrictScalars A) ∘ₗ (Ideal.span {a} : Ideal A).mkQ
  have hf : Function.Surjective f :=
    (Submodule.mkQ_surjective N).comp (Submodule.mkQ_surjective _)
  have hk : LinearMap.ker f = Ideal.span {a, b} := by
    ext x
    have h1 : x ∈ LinearMap.ker f ↔ Ideal.Quotient.mk (Ideal.span {a}) x ∈ N := by
      rw [LinearMap.mem_ker]
      exact Submodule.Quotient.mk_eq_zero N
    rw [h1, Ideal.mem_span_pair, hN, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [LinearMap.lsmul_apply, smul_eq_mul, ← map_mul, Ideal.Quotient.eq,
        Ideal.mem_span_singleton'] at hy
      obtain ⟨c, hc⟩ := hy
      exact ⟨-c, y, by linear_combination -hc⟩
    · rintro ⟨c, y, h⟩
      refine ⟨Ideal.Quotient.mk _ y, ?_⟩
      rw [LinearMap.lsmul_apply, smul_eq_mul, ← map_mul, Ideal.Quotient.eq,
        Ideal.mem_span_singleton']
      exact ⟨-c, by linear_combination -h⟩
  exact ((f.quotKerEquivOfSurjective hf).symm.trans
    (Submodule.quotEquivOfEq _ _ hk)).length_eq

theorem dimension_eq_one_of_add_one (d : WithBot ℕ∞) (hd : d + 1 = 2) : d = 1 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at hd
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd hd (by decide)
    | coe m =>
      have e : ((((m + 1 : ℕ) : ℕ∞)) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_one]
        exact hd
      have h2 : ((m + 1 : ℕ) : ℕ∞) = ((2 : ℕ) : ℕ∞) := WithBot.coe_inj.mp e
      have h3 : m + 1 = 2 := Nat.cast_injective h2
      have h4 : m = 1 := by omega
      subst h4
      rfl

theorem length_quotient_sum_ord (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (b : A) :
    (∑ᶠ (P : PrimeSpectrum (A ⧸ Ideal.span {a}))
        (_ : ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) = 1),
        length (Localization.AtPrime P.asIdeal)
          (LocalizedModule P.asIdeal.primeCompl (A ⧸ Ideal.span {a})) *
            ordMod P (Ideal.Quotient.mk (Ideal.span {a}) b)) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b := by
  have hmem : ∀ P : PrimeSpectrum (A ⧸ Ideal.span {a}),
      a ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal := by
    intro P
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a)]
    exact zero_mem _
  refine finsum_mem_eq_of_bijOn
    (s := {P : PrimeSpectrum (A ⧸ Ideal.span {a}) |
      ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) = 1})
    (t := {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal})
    (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a}))) ⟨?_, ?_, ?_⟩ ?_
  · intro P hP
    refine ⟨(height_one_iff_dim_one h2 ha _ (hmem P)).2 ?_, hmem P⟩
    rw [← dim_quot_comap]
    exact hP
  · exact (PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective).injOn
  · rintro p ⟨hp, hap⟩
    have : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a}))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
      exact (Ideal.span_singleton_le_iff_mem _).2 hap
    obtain ⟨P, rfl⟩ := this
    refine ⟨P, ?_, rfl⟩
    change ringKrullDim _ = 1
    rw [dim_quot_comap]
    exact (height_one_iff_dim_one h2 ha _ hap).1 hp
  · intro P _
    rw [length_loc_quot, ordMod_quot]

theorem length_quotient_pair_formula (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (b : A)
    (hfin : length A (A ⧸ Ideal.span {a, b}) ≠ ⊤) :
    length A (A ⧸ Ideal.span {a, b}) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b := by
  by_cases hu : IsUnit a
  · have h1 : Subsingleton (A ⧸ Ideal.span {a}) :=
      Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 hu)
    have h3 : Subsingleton (A ⧸ Ideal.span {a, b}) :=
      Ideal.Quotient.subsingleton_iff.2
        (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hu)
    have h4 : ∀ p : PrimeSpectrum A, a ∉ p.asIdeal := fun p hp =>
      p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
    simp [h4]
  · have hm : a ∈ IsLocalRing.maximalIdeal A := hu
    have hnt : Nontrivial (A ⧸ Ideal.span {a}) :=
      Ideal.Quotient.nontrivial_iff.2 (fun h => hu (Ideal.span_singleton_eq_top.1 h))
    have hloc : IsLocalRing (A ⧸ Ideal.span {a}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hd := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha) hm
    have hd1 : ringKrullDim (A ⧸ Ideal.span {a}) = 1 := by
      rw [h2] at hd
      exact dimension_eq_one_of_add_one _ hd
    have key := (dimOneFormula (A ⧸ Ideal.span {a}) (A ⧸ Ideal.span {a})
      (Ideal.Quotient.mk (Ideal.span {a}) b) hd1 (by rw [length_quotient_cokernel]; exact hfin)).2
    rw [length_quotient_cokernel, length_quotient_kernel, length_quotient_sum_ord h2 ha] at key
    exact key

end

theorem length_two_generator_quotient : LocalLengthMultiplicativity := by
  intro A _ _ _ _ a b h2 ha hb hfin
  have hfin' : length A (A ⧸ Ideal.span {b, a}) ≠ ⊤ := by rwa [Set.pair_comm]
  have h1 := length_quotient_pair_formula h2 ha b hfin
  have h1' := length_quotient_pair_formula h2 hb a hfin'
  have hs := length_ker_swap a b ha hb
  have ht := length_ker_ne_top a b ha hb hfin
  refine ⟨h1, ⟨hs, ht⟩, ?_⟩
  rw [Set.pair_comm, h1, ← hs] at h1'
  exact ENat.add_right_injective_of_ne_top ht h1'

end ReciprocityTheory.ChartRestriction.G.AI

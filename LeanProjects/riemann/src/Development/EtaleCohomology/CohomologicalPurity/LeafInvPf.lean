import Development.EtaleCohomology.CohomologicalPurity.LeafHensCut

noncomputable section

namespace LateralTheory.CohomologicalPurity.Hz

variable {A : Type} [CommRing A]

theorem inv_retr (I : Ideal A) (x : A) (hx : Ideal.Quotient.mk I x = 1) :
    ∃ r : Localization.Away x →+* A ⧸ I, r.comp (algebraMap A (Localization.Away x)) = Ideal.Quotient.mk I := by
  have hu0 : IsUnit (Ideal.Quotient.mk I x) := by rw [hx]; exact isUnit_one
  exact ⟨IsLocalization.Away.lift (S := Localization.Away x) (g := Ideal.Quotient.mk I) x hu0,
    IsLocalization.Away.lift_comp (S := Localization.Away x) x hu0⟩

theorem inv_surj (I : Ideal A) (x : A) (hx : Ideal.Quotient.mk I x = 1) (s : Localization.Away x) :
    ∃ a : A, s - algebraMap A (Localization.Away x) a ∈ I.map (algebraMap A (Localization.Away x)) := by
  obtain ⟨⟨a, ⟨u, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) s
  refine ⟨a, ?_⟩
  have h1 := IsLocalization.mk'_spec (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x)
  have h2 : 1 - x ^ n ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hx, one_pow, map_one, sub_self]
  rw [← h1]
  have h3 : IsLocalization.mk' (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x) -
      IsLocalization.mk' (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x) *
        algebraMap A (Localization.Away x) (x ^ n) =
      IsLocalization.mk' (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x) *
        algebraMap A (Localization.Away x) (1 - x ^ n) := by
    rw [map_sub, map_one, mul_sub, mul_one]
  rw [h3]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ h2)

theorem inv_univ (I : Ideal A) (i : A) (hi : i ∈ I) : Univ (algebraMap A (Localization.Away (1 + i))) I := by
  intro B _ J hJ ψ hψ
  have hu : IsUnit (ψ (1 + i)) := by
    have hj : ψ i ∈ Ideal.jacobson ⊥ := hJ.jac (hψ hi)
    have := (Ideal.mem_jacobson_bot.1 hj) 1
    rw [mul_one, add_comm] at this
    rwa [map_add, map_one]
  refine ⟨IsLocalization.Away.lift (1 + i) hu, RingHom.ext fun a => IsLocalization.Away.lift_eq (1 + i) hu a, ?_⟩
  intro χ hχ
  apply IsLocalization.ringHom_ext (Submonoid.powers (1 + i))
  rw [hχ]
  exact RingHom.ext fun a => (IsLocalization.Away.lift_eq (1 + i) hu a).symm

theorem LeafInv_of : LeafInv := by
  intro A _ I i hi
  have hx : Ideal.Quotient.mk I (1 + i) = 1 := by
    rw [map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.2 hi, add_zero]
  refine ⟨Localization.Away (1 + i), inferInstance, algebraMap A (Localization.Away (1 + i)),
    ⟨?_, inv_retr I _ hx, inv_surj I _ hx, inv_univ I i hi⟩, IsLocalization.Away.algebraMap_isUnit (1 + i)⟩
  rw [RingHom.etale_algebraMap]
  exact Algebra.Etale.of_isLocalizationAway (1 + i)

end LateralTheory.CohomologicalPurity.Hz

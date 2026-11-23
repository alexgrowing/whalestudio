import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut Polynomial

namespace LateralTheory.E.NormPf.FFPf

theorem algClosed_of_aic (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (h : GlobalTheory.EtC.AIC R) : IsAlgClosed K := by
  classical
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  have hd : 0 < p.natDegree := Irreducible.natDegree_pos hirr
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    ((Finset.range (p.natDegree + 1)).image p.coeff)
  set d : K := algebraMap R K b with hdd
  have hd0 : d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hint : ∀ i, ∃ r : R, algebraMap R K r = p.coeff i * d := by
    intro i
    by_cases hi : i ≤ p.natDegree
    · obtain ⟨r, hr⟩ := hb (p.coeff i) (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩)
      refine ⟨r, ?_⟩
      rw [hr, Algebra.smul_def, mul_comm]
    · exact ⟨0, by rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp⟩
  have hl : scaleRoots p d ∈ lifts (algebraMap R K) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    by_cases hi : i < p.natDegree
    · obtain ⟨r, hr⟩ := hint i
      refine ⟨r * b ^ (p.natDegree - i - 1), ?_⟩
      rw [map_mul, map_pow, hr, ← hdd, mul_assoc, ← pow_succ']
      congr 2
      omega
    · by_cases he : i = p.natDegree
      · subst he; exact ⟨1, by rw [hp.coeff_natDegree]; simp⟩
      · exact ⟨0, by rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_degree_eq_and_monic hl ((monic_scaleRoots_iff d).mpr hp)
  have hqn : 0 < q.natDegree := by
    rw [natDegree_eq_of_degree_eq hqd, natDegree_scaleRoots]; exact hd
  obtain ⟨r, hr⟩ := h q hqm hqn
  refine ⟨algebraMap R K r / d, ?_⟩
  have e1 := scaleRoots_eval₂_mul (p := p) (RingHom.id K) (algebraMap R K r / d) d
  simp only [RingHom.id_apply, eval₂_id] at e1
  rw [mul_div_cancel₀ _ hd0, ← hq, Polynomial.eval_map, eval₂_at_apply, hr, map_zero] at e1
  exact (mul_eq_zero.mp e1.symm).resolve_left (pow_ne_zero _ hd0)

theorem ffAlg : FFAlg := by
  intro Z _ hZ
  obtain ⟨x⟩ := (inferInstance : Nonempty Z)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen Z V hV
  exact algClosed_of_aic Γ(Z, V) Z.functionField (hZ.2 V hV ⟨x, hxV⟩)

end LateralTheory.E.NormPf.FFPf

end

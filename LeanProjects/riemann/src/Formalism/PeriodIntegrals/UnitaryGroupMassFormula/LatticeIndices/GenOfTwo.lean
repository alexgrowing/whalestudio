import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.QuadRoot

noncomputable section

namespace MassDataIdxEmb

open NumberField IsDedekindDomain Polynomial

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem mem_iff_algebraMap_mem_of_liesOver (P : Ideal (𝓞 E)) (q : Ideal (𝓞 F)) [P.LiesOver q]
    (c : 𝓞 F) : c ∈ q ↔ algebraMap (𝓞 F) (𝓞 E) c ∈ P := by
  rw [Ideal.over_def P q]
  exact Iff.rfl

private theorem exists_mem_not_mem_of_ne_of_isMaximal {R : Type*} [CommRing R] (Q Q' : Ideal R)
    [hQ : Q.IsMaximal] [hQ' : Q'.IsMaximal] (hne : Q ≠ Q') : ∃ a ∈ Q, a ∉ Q' := by
  by_contra h
  push Not at h
  exact hne (hQ.eq_of_le hQ'.ne_top (fun x hx => h x hx))

theorem gen_of_two (h2 : Module.finrank F E = 2) (p : HeightOneSpectrum (𝓞 F)) (Q Q' : Ideal (𝓞 E)) [hQ : Q.IsMaximal]
    [hQ' : Q'.IsMaximal] (hne : Q ≠ Q') [Q.LiesOver p.asIdeal] [Q'.LiesOver p.asIdeal] :
    ∃ a : 𝓞 E, ∃ c0 c1 : 𝓞 F, (∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ≠ a) ∧
      a * a + algebraMap (𝓞 F) (𝓞 E) c1 * a + algebraMap (𝓞 F) (𝓞 E) c0 = 0 ∧
      minpoly (𝓞 F) a = X ^ 2 + C c1 * X + C c0 ∧ (minpoly (𝓞 F) a).natDegree = 2 ∧
      c0 ∈ p.asIdeal ∧ c1 ∉ p.asIdeal := by
  obtain ⟨a, ha, ha'⟩ := exists_mem_not_mem_of_ne_of_isMaximal Q Q' hne
  have hnot : ∀ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ≠ a := by
    intro c hc
    apply ha'
    have hcQ : c ∈ p.asIdeal := (mem_iff_algebraMap_mem_of_liesOver Q p.asIdeal c).2 (by rw [hc]; exact ha)
    rw [← hc]
    exact (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal c).1 hcQ
  have hint_r : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hFE : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hfield : minpoly F (algebraMap (𝓞 E) E a) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hint_r
  have hle : (minpoly (𝓞 F) a).natDegree ≤ 2 := by
    have h : (minpoly F (algebraMap (𝓞 E) E a)).natDegree ≤ Module.finrank F E := by
      apply minpoly.natDegree_le
    rw [hfield, (minpoly.monic hint_r).natDegree_map, h2] at h
    exact h
  have hpos : 0 < (minpoly (𝓞 F) a).natDegree := minpoly.natDegree_pos hint_r
  have hne1 : (minpoly (𝓞 F) a).natDegree ≠ 1 := by
    intro h1
    have hX := (minpoly.monic hint_r).eq_X_add_C h1
    have hev := minpoly.aeval (𝓞 F) a
    rw [hX] at hev
    simp only [map_add, aeval_X, aeval_C] at hev
    apply hnot (-(minpoly (𝓞 F) a).coeff 0)
    rw [map_neg]
    linear_combination -hev
  have hdeg : (minpoly (𝓞 F) a).natDegree = 2 := by omega
  have hP : minpoly (𝓞 F) a =
      X ^ 2 + C ((minpoly (𝓞 F) a).coeff 1) * X + C ((minpoly (𝓞 F) a).coeff 0) := by
    refine (minpoly.monic hint_r).as_sum.trans ?_
    rw [hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, mul_one,
      zero_add]
    ring
  have hev := minpoly.aeval (𝓞 F) a
  rw [hP] at hev
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C] at hev
  have heq : a * a + algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1) * a +
      algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0) = 0 := by
    linear_combination hev
  have hc0 : (minpoly (𝓞 F) a).coeff 0 ∈ p.asIdeal := by
    refine (mem_iff_algebraMap_mem_of_liesOver Q p.asIdeal _).2 ?_
    have h : algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0) =
        -(a * (a + algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1))) := by
      linear_combination heq
    rw [h]
    exact neg_mem (Q.mul_mem_right _ ha)
  have hc1 : (minpoly (𝓞 F) a).coeff 1 ∉ p.asIdeal := by
    intro h
    have h1 := (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal _).1 h
    have h0 := (mem_iff_algebraMap_mem_of_liesOver Q' p.asIdeal _).1 hc0
    have haa : a * a ∈ Q' := by
      have h' : a * a = -(algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 1) * a +
          algebraMap (𝓞 F) (𝓞 E) ((minpoly (𝓞 F) a).coeff 0)) := by
        linear_combination heq
      rw [h']
      exact neg_mem (add_mem (Q'.mul_mem_right _ h1) h0)
    rcases hQ'.isPrime.mem_or_mem haa with h | h <;> exact ha' h
  exact ⟨a, _, _, hnot, heq, hP, hdeg, hc0, hc1⟩

private theorem finitePlace_embedding_eq_algebraMap (p : HeightOneSpectrum (𝓞 F)) (k : F) :
    FinitePlace.embedding p k = algebraMap F (p.adicCompletion F) k := rfl

private theorem norm_algebraMap_adicCompletion_lt_one_of_mem (p : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F)
    (hc : c ∈ p.asIdeal) : ‖algebraMap (𝓞 F) (p.adicCompletion F) c‖ < 1 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (p.adicCompletion F), ← finitePlace_embedding_eq_algebraMap]
  exact (FinitePlace.norm_lt_one_iff_mem F p c).2 hc

private theorem norm_algebraMap_adicCompletion_eq_one_of_not_mem (p : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F)
    (hc : c ∉ p.asIdeal) : ‖algebraMap (𝓞 F) (p.adicCompletion F) c‖ = 1 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (p.adicCompletion F), ← finitePlace_embedding_eq_algebraMap]
  exact (FinitePlace.norm_eq_one_iff_notMem F p c).2 hc

theorem emb_of_two (h2 : Module.finrank F E = 2) (p : HeightOneSpectrum (𝓞 F)) (Q Q' : Ideal (𝓞 E))
    [Q.IsMaximal] [Q'.IsMaximal] (hne : Q ≠ Q') [Q.LiesOver p.asIdeal] [Q'.LiesOver p.asIdeal] :
    Nonempty (E →ₐ[F] p.adicCompletion F) := by
  obtain ⟨a, c0, c1, -, -, hP, hdeg, hc0, hc1⟩ := gen_of_two h2 p Q Q' hne
  have hint_r : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hFE : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hfield : minpoly F (algebraMap (𝓞 E) E a) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hint_r
  have hbint : IsIntegral F (algebraMap (𝓞 E) E a) := IsIntegral.of_finite F _
  have htop : IntermediateField.adjoin F {algebraMap (𝓞 E) E a} = ⊤ := by
    rw [Field.primitive_element_iff_minpoly_natDegree_eq, hfield,
      (minpoly.monic hint_r).natDegree_map, hdeg, h2]
  obtain ⟨x, hx⟩ := quad_root
    (algebraMap (𝓞 F) (p.adicCompletion F) c0) (algebraMap (𝓞 F) (p.adicCompletion F) c1)
    (norm_algebraMap_adicCompletion_eq_one_of_not_mem p c1 hc1) (norm_algebraMap_adicCompletion_lt_one_of_mem p c0 hc0)
  have hroot : aeval x (minpoly F (algebraMap (𝓞 E) E a)) = 0 := by
    rw [hfield, aeval_map_algebraMap F, hP]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    linear_combination hx
  have hpb : aeval x (minpoly F (IntermediateField.adjoin.powerBasis hbint).gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    exact hroot
  let e : ↥(IntermediateField.adjoin F {algebraMap (𝓞 E) E a}) ≃ₐ[F] E :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  exact ⟨((IntermediateField.adjoin.powerBasis hbint).lift x hpb).comp e.symm.toAlgHom⟩

end MassDataIdxEmb

import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSqAbsNormOfInert

open NumberField Module Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_star_ne (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) : ∃ a : K, star a ≠ a := by
  obtain ⟨hTC, hconj, -⟩ := hK
  by_contra h
  push_neg at h
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace K) := inferInstance
  have hc := hTC.isComplex w
  rw [NumberField.InfinitePlace.isComplex_iff] at hc
  apply hc
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext a
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hconj, h]

theorem star_algebraMap (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (u : F) :
    star (algebraMap F K u) = algebraMap F K u :=
  (hF _).2 ⟨u, rfl⟩

theorem exists_decomp (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {a : K}
    (ha : star a ≠ a) (x : K) : ∃ u v : F, x = algebraMap F K u + algebraMap F K v * a := by
  have hb : a - star a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  obtain ⟨w, hw⟩ : ∃ w : K, w * (a - star a) = x - star x :=
    ⟨(x - star x) / (a - star a), div_mul_cancel₀ _ hb⟩
  have hsw : star w = w := by
    have h1 := congrArg star hw
    rw [star_mul', star_sub, star_sub, star_star, star_star] at h1
    apply mul_right_cancel₀ hb
    linear_combination -h1 - hw
  obtain ⟨v, hv⟩ := (hF w).1 hsw
  have hz : star (x - w * a) = x - w * a := by
    rw [star_sub, star_mul', hsw]
    linear_combination hw
  obtain ⟨u, hu⟩ := (hF _).1 hz
  exact ⟨u, v, by rw [hu, hv]; ring⟩

theorem finrank_eq_two (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : finrank F K = 2 := by
  obtain ⟨a, ha⟩ := exists_star_ne hK
  have hli : LinearIndependent F ![(1 : K), a] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply ha
      have htK : algebraMap F K t ≠ 0 := (_root_.map_ne_zero _).mpr ht
      have hA : a = algebraMap F K (-s / t) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
        rw [map_div₀, map_neg, eq_div_iff htK]
        linear_combination hst
      exact (hF a).2 ⟨_, hA.symm⟩
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : K), a]) := by
    intro x _
    obtain ⟨u, v, rfl⟩ := exists_decomp hF ha x
    apply Submodule.add_mem
    · rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, by simp⟩)
  rw [Module.finrank_eq_card_basis (Basis.mk hli hsp)]
  simp

theorem adjoin_eq_top (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {a : K}
    (ha : star a ≠ a) : Algebra.adjoin F {a} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨u, v, rfl⟩ := exists_decomp hF ha x
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ u)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ v) (Algebra.subset_adjoin (Set.mem_singleton a)))

theorem coe_algebraMap (z : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) z) = algebraMap F K (algebraMap (𝓞 F) F z) := by
  rfl

theorem exists_int_of_star_eq (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K))
    (y : 𝓞 K) (hy : star (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) K y) :
    ∃ z : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) z = y := by
  obtain ⟨u, hu⟩ := (hF _).1 hy
  have hint : IsIntegral ℤ u := by
    have h1 : IsIntegral ℤ (algebraMap F K u) := by
      rw [hu]; exact RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algebraMap_iff (algebraMap F K).injective).mp h1
  refine ⟨⟨u, hint⟩, ?_⟩
  apply RingOfIntegers.ext
  exact (coe_algebraMap (F := F) (K := K) ⟨u, hint⟩).trans hu

theorem isTotallyReal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : IsTotallyReal F := by
  obtain ⟨-, hconj, -⟩ := hK
  refine ⟨fun w => ?_⟩
  obtain ⟨v, rfl⟩ := NumberField.InfinitePlace.comap_surjective (k := F) (K := K) w
  try dsimp only
  rw [← NumberField.InfinitePlace.mk_embedding v, NumberField.InfinitePlace.comap_mk]
  by_contra h
  rw [NumberField.InfinitePlace.not_isReal_iff_isComplex, NumberField.InfinitePlace.isComplex_mk_iff] at h
  apply h
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext u
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hconj, star_algebraMap hF]

theorem minpoly_eq (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (θ t : 𝓞 K)
    (ht : algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ)) (hne : θ ≠ t) :
    aeval θ (derivative (minpoly (𝓞 F) θ)) = θ - t := by
  have ht' : star (algebraMap (𝓞 K) K t) = algebraMap (𝓞 K) K θ := by rw [ht, star_star]
  obtain ⟨s, hs⟩ := exists_int_of_star_eq hF (θ + t) (by rw [map_add, star_add, ht', ← ht, add_comm])
  obtain ⟨p, hp⟩ := exists_int_of_star_eq hF (θ * t) (by rw [map_mul, star_mul', ht', ← ht, mul_comm])
  obtain ⟨q, hq⟩ : ∃ q : Polynomial (𝓞 F), q = X ^ 2 - C s * X + C p := ⟨_, rfl⟩
  have hqdeg : q.natDegree = 2 := by rw [hq]; compute_degree!
  have hqm : q.Monic := by rw [hq]; monicity!
  have hroot : aeval θ q = 0 := by
    rw [hq]
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hs, hp]
    ring
  have hint : IsIntegral (𝓞 F) θ := by
    first
      | exact Algebra.IsIntegral.isIntegral θ
      | exact IsIntegral.tower_top (A := 𝓞 F) (RingOfIntegers.isIntegral θ)
      | exact (Algebra.IsIntegral.isIntegral (R := ℤ) θ).tower_top
  have hdvd : minpoly (𝓞 F) θ ∣ q := minpoly.isIntegrallyClosed_dvd hint hroot
  have hdeg2 : 2 ≤ (minpoly (𝓞 F) θ).natDegree := by
    by_contra hlt
    push_neg at hlt
    have h1 : (minpoly (𝓞 F) θ).natDegree = 1 := by
      have := minpoly.natDegree_pos hint
      omega
    have hd1 : (minpoly (𝓞 F) θ).degree = 1 := by
      rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hint), h1]
      rfl
    have hr : θ ∈ (algebraMap (𝓞 F) (𝓞 K)).range := by
      first
        | exact minpoly.mem_range_of_degree_eq_one (𝓞 F) θ hd1
        | exact minpoly.mem_range_of_degree_eq_one hd1
        | exact minpoly.mem_range_of_degree_eq_one (𝓞 F) hd1
    obtain ⟨z, hz⟩ := hr
    apply hne
    apply RingOfIntegers.ext
    have hfx : star (algebraMap (𝓞 K) K θ) = algebraMap (𝓞 K) K θ := by
      rw [← hz, coe_algebraMap]
      exact star_algebraMap hF _
    exact (ht.trans hfx).symm
  have heq : q = minpoly (𝓞 F) θ :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hqm hdvd (by rw [hqdeg]; exact hdeg2)
  rw [← heq, hq]
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_X_pow, derivative_C,
    derivative_X, zero_mul, mul_one, zero_add, add_zero, map_add, map_sub, map_mul, map_pow,
    aeval_X, aeval_C, map_natCast, hs]
  first
    | ring
    | (norm_num; ring)
    | norm_num
    | (push_cast; ring)

theorem differentIdeal_eq_top (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) :
    differentIdeal (𝓞 F) (𝓞 K) = ⊤ := by
  obtain ⟨-, -, hmax⟩ := hK
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨θ, t, ht, hθt⟩ := hmax P hP
  have hne' : θ ≠ t := fun h => hθt (by rw [h, sub_self]; exact P.zero_mem)
  have hstar : star (algebraMap (𝓞 K) K θ) ≠ algebraMap (𝓞 K) K θ := by
    rw [← ht]; exact fun h => hne' (RingOfIntegers.ext h.symm)
  apply hθt
  apply hle
  rw [← minpoly_eq hF θ t ht hne']
  exact aeval_derivative_mem_differentIdeal (A := 𝓞 F) (K := F) (L := K) θ (adjoin_eq_top hF hstar)

theorem natAbs_discr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) :
    (discr K).natAbs = (discr F).natAbs ^ 2 := by
  rw [natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) K (𝓞 K),
    differentIdeal_eq_top hK hF, Ideal.absNorm_top, one_mul, finrank_eq_two hK hF]

theorem discr_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) : 0 < discr F := by
  haveI := isTotallyReal hK hF
  first
    | exact NumberField.discr_pos_of_isTotallyReal F
    | (have h := NumberField.sign_discr F
       rw [IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero] at h
       exact Int.sign_eq_one_iff_pos.mp h)

end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation

namespace Formalism.HermitianLattices.Ext.L3

theorem discrTower : DiscrTower := by
  intro K F _ _ _ _ _ _ hK hF
  have hpos := QuadraticExtensionConjugation.discr_pos hK hF
  have h1 := QuadraticExtensionConjugation.natAbs_discr hK hF
  have hTC : IsTotallyComplex K := by
    obtain ⟨h, -, -⟩ := hK
    exact h
  have hA : |(discr K : ℝ)| = (discr F : ℝ) ^ 2 := by
    have h2 := congrArg (fun n : ℕ => (n : ℝ)) h1
    simp only [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] at h2
    rw [h2, sq_abs]
  have hdeg : finrank ℚ F = Formalism.HermitianLatticesTheory.fDeg K := by
    have e1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    have e2 := Module.finrank_mul_finrank ℚ F K
    have e3 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    have e4 : NumberField.InfinitePlace.nrRealPlaces K = 0 := by
      first
        | exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero
        | exact IsTotallyComplex.nrRealPlaces_eq_zero
        | exact NumberField.InfinitePlace.nrRealPlaces_eq_zero_iff.mpr hTC
        | exact NumberField.nrRealPlaces_eq_zero_iff.mpr hTC
        | (haveI : IsEmpty {w : NumberField.InfinitePlace K // w.IsReal} :=
             ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w.1)) w.2⟩
           simp [NumberField.InfinitePlace.nrRealPlaces])
        | (unfold NumberField.InfinitePlace.nrRealPlaces
           rw [Fintype.card_eq_zero_iff]
           exact ⟨fun w => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hTC.isComplex w.1)) w.2⟩)
    rw [QuadraticExtensionConjugation.finrank_eq_two hK hF] at e2
    unfold Formalism.HermitianLatticesTheory.fDeg
    omega
  refine ⟨hA, hdeg, ?_⟩
  have hF0 : (0 : ℝ) < discr F := by exact_mod_cast hpos
  have hd : 0 < Formalism.HermitianLatticesTheory.fDeg K := by
    unfold Formalism.HermitianLatticesTheory.fDeg
    exact Fintype.card_pos
  have hd0 : ((Formalism.HermitianLatticesTheory.fDeg K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold Formalism.HermitianLatticesTheory.vInv
  rw [show ∀ x : ℝ, 2 * (x / 2) = x from fun x => by ring, hA, ← Real.rpow_natCast (discr F : ℝ) 2,
    ← Real.rpow_mul hF0.le, ← Real.rpow_natCast _ (Formalism.HermitianLatticesTheory.fDeg K), ← Real.rpow_mul hF0.le]
  conv_lhs => rw [← Real.rpow_one (discr F : ℝ)]
  congr 1
  first
    | (push_cast; field_simp)
    | (push_cast; field_simp; ring)
    | field_simp
    | (field_simp; ring)

end Formalism.HermitianLattices.Ext.L3

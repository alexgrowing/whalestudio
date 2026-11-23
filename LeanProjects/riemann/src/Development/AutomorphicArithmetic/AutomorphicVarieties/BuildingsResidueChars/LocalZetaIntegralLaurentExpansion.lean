import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdDefs

noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem UpperTheory.local_zeta_integral_laurent_expansion :
    UpperTheory.V.Z.Gam.LdLaurent := by
  intro F _ _ _ _ m _ _ _ μ _ α c hc hzero Φ hΦ
  obtain ⟨A, hA⟩ := hΦ.exists_ordDet_ge
  obtain ⟨K, hK, hKc⟩ := hc.exists_compact_tile
  obtain ⟨B, hB⟩ := exists_valBall_of_isCompact (hK.image Units.continuous_val)
  obtain ⟨J, hJ⟩ := hΦ.exists_eq_zero_of_small B
  have hm : (0 : ℤ) < m := by
    have := NeZero.pos m
    omega
  let sh : ℤ → Set (GL (Fin m) F) := fun k => {g | ordDet g = k}
  refine ⟨Finset.Icc (-((m : ℤ) * A)) (J * m), fun k => ∫ g in sh k, Φ g * c g ∂μ, ?_⟩
  intro s hs
  have hint := hc.integrable_zeta μ hΦ hs
  have hmeas : ∀ k, MeasurableSet (sh k) := fun k => (isClopen_shell F m k).isClosed.measurableSet
  have hdisj : Pairwise (fun i j => Disjoint (sh i) (sh j)) := by
    intro i j hij
    exact Set.disjoint_left.2 fun g hi hj => hij (hi.symm.trans hj)
  have huniv : (⋃ k, sh k) = Set.univ := Set.iUnion_eq_univ_iff.2 fun g => ⟨ordDet g, rfl⟩
  have hsplit := integral_iUnion hmeas hdisj hint.integrableOn
  rw [huniv, setIntegral_univ] at hsplit
  rw [hsplit]
  have hshell : ∀ k, ∫ g in sh k, Φ g * detPow g s * c g ∂μ = (∫ g in sh k, Φ g * c g ∂μ) * qs F s ^ k := by
    intro k
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (hmeas k) fun g hg => ?_
    have hg' : ordDet g = k := hg
    rw [detPow_eq_qs_zpow, hg']
    ring
  simp_rw [hshell]
  apply tsum_eq_sum
  intro k hk
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk0 : ∫ g in sh k, Φ g * c g ∂μ = 0 := by
    rcases hk with hk | hk
    · apply setIntegral_eq_zero_of_forall_eq_zero
      intro g hg
      have hg' : ordDet g = k := hg
      have hΦ0 : Φ g = 0 := by
        by_contra hne
        have := hA g hne
        linarith
      rw [hΦ0, zero_mul]
    · have hcongr : ∫ g in sh k, Φ g * c g ∂μ = ∫ g in sh k, Φ 0 * c g ∂μ := by
        refine setIntegral_congr_fun (hmeas k) fun g hg => ?_
        have hg' : ordDet g = k := hg
        by_cases hcg : c g = 0
        · simp [hcg]
        · congr 1
          have hgh : centralUnif F m ^ (k / (m : ℤ)) * (centralUnif F m ^ (-(k / (m : ℤ))) * g) = g := by
            rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
          have hordh : ordDet (centralUnif F m ^ (-(k / (m : ℤ))) * g) = k % m := by
            rw [ordDet_centralUnif_zpow_mul, hg', Int.emod_def]
            ring
          have htile : centralUnif F m ^ (-(k / (m : ℤ))) * g ∈ tile F m 0 := by
            simp only [tile, Set.mem_setOf_eq, zero_mul, zero_add]
            rw [hordh]
            exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩
          have hch : c (centralUnif F m ^ (-(k / (m : ℤ))) * g) ≠ 0 := by
            rw [← hgh, hc.zpow_mul] at hcg
            exact right_ne_zero_of_mul hcg
          have hhK := hKc _ htile hch
          have hball := hB _ ⟨_, hhK, rfl⟩
          have hjJ : J ≤ k / (m : ℤ) := Int.le_ediv_of_mul_le hm hk.le
          rw [← hgh]
          exact hJ _ hjJ _ hball
      rw [hcongr, integral_const_mul, hzero k, mul_zero]
  rw [hk0, zero_mul]

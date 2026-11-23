import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.LatticeSum

open NumberField.mixedEmbedding
open scoped Classical

theorem infinitePlace_eq (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    (hc : IsTotallyComplex K) (w w' : InfinitePlace K) : w = w' := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h3 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have h4 : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h3]
    omega
  exact Fintype.card_le_one_iff.1 h4.le w w'

theorem norm_mixedEmbedding (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    (hc : IsTotallyComplex K) (x : K) : ‖mixedEmbedding K x‖ = ‖embC K x‖ := by
  rw [norm_eq_sup'_normAtPlace]
  unfold embC
  rw [InfinitePlace.norm_embedding_eq]
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun w _ => ?_
    rw [normAtPlace_apply, infinitePlace_eq K h2 hc w (Classical.arbitrary _)]
  · refine le_trans (le_of_eq (normAtPlace_apply _ x).symm) ?_
    exact Finset.le_sup' (fun w => normAtPlace w (mixedEmbedding K x)) (Finset.mem_univ _)

theorem finrank_span_latticeBasis (K : Type) [Field K] [NumberField K] :
    Module.finrank ℤ (Submodule.span ℤ (Set.range (latticeBasis K))) = Module.finrank ℚ K := by
  rw [finrank_span_eq_card ((latticeBasis K).linearIndependent.restrict_scalars (R := ℤ)
    (by simpa using Int.cast_injective))]
  rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank]

theorem summable_inv_one_add_norm_pow_four :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ N : ℕ, N ≠ 0 →
  Summable (fun ξ : {ξ : K // ∃ a : 𝓞 K, (N : K) * ξ = a} => ((1 + ‖embC K ξ.1‖) ^ 4)⁻¹) := by
  intro K _ _ h2 hc N hN
  have hrank : Module.finrank ℤ (Submodule.span ℤ (Set.range (latticeBasis K))) < 4 := by
    rw [finrank_span_latticeBasis, h2]
    omega
  have hs := ZLattice.summable_norm_pow_inv (Submodule.span ℤ (Set.range (latticeBasis K))) 4 hrank
  have hmem : ∀ ξ : {ξ : K // ∃ a : 𝓞 K, (N : K) * ξ = a},
      mixedEmbedding K ((N : K) * ξ.1) ∈ Submodule.span ℤ (Set.range (latticeBasis K)) := by
    rintro ⟨ξ, a, ha⟩
    rw [ha]
    exact (mem_span_latticeBasis K).mpr ⟨a, rfl⟩
  let f : {ξ : K // ∃ a : 𝓞 K, (N : K) * ξ = a} →
      Submodule.span ℤ (Set.range (latticeBasis K)) := fun ξ => ⟨_, hmem ξ⟩
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hinj : Function.Injective f := by
    intro ξ η h
    have h1 : mixedEmbedding K ((N : K) * ξ.1) = mixedEmbedding K ((N : K) * η.1) :=
      congrArg Subtype.val h
    exact Subtype.ext (mul_left_cancel₀ hN' (mixedEmbedding_injective K h1))
  have h0 : Summable fun z : Submodule.span ℤ (Set.range (latticeBasis K)) =>
      (if z = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq _ (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ξ => ?_)
    (((hs.mul_left ((N : ℝ) ^ 4)).add h0).comp_injective hinj)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hnorm : ‖f ξ‖ = N * ‖embC K ξ.1‖ := by
    change ‖mixedEmbedding K ((N : K) * ξ.1)‖ = _
    rw [norm_mixedEmbedding K h2 hc]
    unfold embC
    simp
  simp only [Function.comp_apply]
  by_cases hz : f ξ = 0
  · rw [if_pos hz]
    have h1 : ((1 + ‖embC K ξ.1‖) ^ 4)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg (embC K ξ.1)]))
    have h3 : 0 ≤ (N : ℝ) ^ 4 * ‖f ξ‖⁻¹ ^ 4 := by positivity
    linarith
  · rw [if_neg hz, add_zero, hnorm]
    have ht : 0 < ‖embC K ξ.1‖ := by
      have : 0 < ‖f ξ‖ := norm_pos_iff.mpr hz
      rw [hnorm] at this
      exact (mul_pos_iff_of_pos_left hNpos).mp this
    have he : (N : ℝ) ^ 4 * ((N : ℝ) * ‖embC K ξ.1‖)⁻¹ ^ 4 = (‖embC K ξ.1‖ ^ 4)⁻¹ := by
      field_simp
    rw [he]
    gcongr
    linarith

end GlobalTheory.CompanionTheory.LatticeSum

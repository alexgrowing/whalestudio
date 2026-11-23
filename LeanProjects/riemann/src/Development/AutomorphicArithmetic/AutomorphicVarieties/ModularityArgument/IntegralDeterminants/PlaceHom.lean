import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousExtensionAdicCompletion

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace UpperTheory.V.Z.Int

private theorem val_le_one_iff {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* Qbar l) (u : HeightOneSpectrum (𝓞 E))
    (hu : ∀ x : E, u.valuation E x < 1 ↔ ‖c x‖ < 1) (x : E) :
    u.valuation E x ≤ 1 ↔ ‖c x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : 0 < u.valuation E x := zero_lt_iff.2 ((map_ne_zero _).2 hx)
  have h1 : 0 < ‖c x‖ := norm_pos_iff.2 ((map_ne_zero c).2 hx)
  have h := hu x⁻¹
  rw [map_inv₀, map_inv₀, norm_inv, inv_lt_one₀ h0, inv_lt_one₀ h1] at h
  rw [← not_lt, ← not_lt, h]

theorem placeHom : PlaceHom := by
  intro l _ ι E _ _ τ
  let c : E →+* Qbar l := ι.symm.toRingHom.comp τ
  have hc : ∀ x, c x = ι.symm (τ x) := fun _ => rfl
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l c
  obtain ⟨j, hj, hjE⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l c u hu
  have hjx : ∀ x : E, j (algebraMap E (u.adicCompletion E) x) = c x :=
    fun x => DFunLike.congr_fun hjE x
  refine ⟨u, ι.toRingHom.comp j, fun x => ?_, fun x => ?_, fun w => ?_⟩
  · change ι (j (algebraMap E (u.adicCompletion E) x)) = τ x
    rw [hjx, hc, RingEquiv.apply_symm_apply]
  · have hnu : ∀ y, nu ι ((ι.toRingHom.comp j) y) = ‖j y‖ := fun y => by
      change ‖ι.symm (ι (j y))‖ = _
      rw [RingEquiv.symm_apply_apply]
    rw [hnu]
    have hB : IsClopen {y : u.adicCompletion E | ‖j y‖ ≤ 1} := by
      have := (IsUltrametricDist.isClopen_closedBall (0 : Qbar l) one_ne_zero).preimage hj
      simpa [Set.preimage, Metric.closedBall] using this
    have hC : IsClopen {y : u.adicCompletion E | Valued.v y ≤ 1} :=
      Valued.isClopen_integer (u.adicCompletion E)
    have hT : IsClosed {y : u.adicCompletion E | ‖j y‖ ≤ 1 ↔ Valued.v y ≤ 1} := by
      have : {y : u.adicCompletion E | ‖j y‖ ≤ 1 ↔ Valued.v y ≤ 1} =
          ({y | ‖j y‖ ≤ 1} ∩ {y | Valued.v y ≤ 1}) ∪
            ({y | ‖j y‖ ≤ 1}ᶜ ∩ {y | Valued.v y ≤ 1}ᶜ) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      rw [this]
      exact (hB.isClosed.inter hC.isClosed).union (hB.compl.isClosed.inter hC.compl.isClosed)
    refine (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) (K := E) u).induction_on
      (p := fun y => ‖j y‖ ≤ 1 ↔ Valued.v y ≤ 1) x hT fun a => ?_
    have hv : Valued.v (algebraMap E (u.adicCompletion E) a) = u.valuation E a :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u a
    rw [hjx, hv, val_le_one_iff c u hu a]
  · have hw : ∀ a : 𝓞 E, nu ι (τ a) = ‖c a‖ := fun _ => rfl
    have hmem : ∀ a : 𝓞 E, a ∈ u.asIdeal ↔ ‖c a‖ < 1 := fun a => by
      rw [← hu, HeightOneSpectrum.valuation_lt_one_iff_mem]
    simp only [Ov, Finset.mem_filter, Finset.mem_univ, true_and, hw]
    constructor
    · intro h
      exact HeightOneSpectrum.ext (Ideal.ext fun a => (h a).trans (hmem a).symm)
    · rintro rfl
      exact hmem

end UpperTheory.V.Z.Int

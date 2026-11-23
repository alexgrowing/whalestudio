import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPlaceCentredSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField IsDedekindDomain Ideal

namespace PlaceCentredSum

variable {L K : Type} [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]

noncomputable def below (v : FinitePlace K) : HeightOneSpectrum (𝓞 L) where
  asIdeal := v.maximalIdeal.asIdeal.under (𝓞 L)
  isPrime := inferInstance
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.maximalIdeal.ne_bot
    exact comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

instance (v : FinitePlace K) : v.maximalIdeal.asIdeal.LiesOver (below (L := L) v).asIdeal := ⟨rfl⟩

noncomputable def deg (L : Type) [Field L] [NumberField L] [Algebra L K] (v : FinitePlace K) : ℕ :=
  v.maximalIdeal.asIdeal.ramificationIdx (𝓞 L) * v.maximalIdeal.asIdeal.inertiaDeg (𝓞 L)

lemma toNNReal_pow {b c : NNReal} (hc : c ≠ 0) (hb : b ≠ 0) {f : ℕ} (hf : f ≠ 0) (h : c = b ^ f)
    (z : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal hc z = WithZeroMulInt.toNNReal hb z ^ f := by
  subst h
  rcases eq_or_ne z 0 with rfl | hz
  · simp [hf]
  · rw [WithZeroMulInt.toNNReal_neg_apply _ hz, WithZeroMulInt.toNNReal_neg_apply _ hz,
      ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem apply_algebraMap (v : FinitePlace K) (x : L) :
    v (algebraMap L K x) = FinitePlace.mk (below v) x ^ deg L v := by
  have hQ : (below (L := L) v).asIdeal ≠ ⊥ := (below v).ne_bot
  have hf : (below (L := L) v).asIdeal.inertiaDeg' v.maximalIdeal.asIdeal ≠ 0 :=
    (inertiaDeg'_pos' _ _).ne'
  have hN := absNorm_eq_pow_inertiaDeg'_of_liesOver v.maximalIdeal.asIdeal (below (L := L) v).asIdeal
    inferInstance hQ
  rw [← FinitePlace.norm_embedding_eq v, FinitePlace.mk_apply, FinitePlace.norm_embedding',
    FinitePlace.norm_embedding', ← HeightOneSpectrum.valuation_liesOver K (below (L := L) v) v.maximalIdeal, map_pow,
    toNNReal_pow _ (NumberField.HeightOneSpectrum.absNorm_ne_zero (below (L := L) v)) hf (by rw [hN]; push_cast; rfl), deg,
    ramificationIdx'_eq_ramificationIdx _ _ hQ, inertiaDeg'_eq_inertiaDeg, ← pow_mul]
  push_cast
  rw [mul_comm]

lemma deg_ne_zero (v : FinitePlace K) : deg L v ≠ 0 := by
  refine mul_ne_zero ?_ (inertiaDeg_pos _ _).ne'
  rw [← ramificationIdx'_eq_ramificationIdx _ _ (below (L := L) v).ne_bot]
  exact IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ (below v).ne_bot

theorem centred_iff (O : Subalgebra ℤ L) (m : Ideal O) (v : FinitePlace K) :
    AbsCentredAt O m (fun u ↦ v (algebraMap L K u)) ↔
      AbsCentredAt O m (fun u ↦ FinitePlace.mk (below v) u) := by
  have h1 : ∀ a : ℝ, 0 ≤ a → (a ^ deg L v ≤ 1 ↔ a ≤ 1) := fun a ha ↦
    pow_le_one_iff_of_nonneg ha (deg_ne_zero v)
  have h2 : ∀ a : ℝ, 0 ≤ a → (a ^ deg L v < 1 ↔ a < 1) := fun a ha ↦
    pow_lt_one_iff_of_nonneg ha (deg_ne_zero v)
  unfold AbsCentredAt
  simp only [apply_algebraMap]
  exact and_congr (forall_congr' fun u ↦ h1 _ (apply_nonneg _ _))
    (forall_congr' fun u ↦ by rw [h2 _ (apply_nonneg _ _)])

theorem neg_log_apply (v : FinitePlace K) (t : L) :
    -Real.log (v (algebraMap L K t)) = deg L v * -Real.log (FinitePlace.mk (below v) t) := by
  rw [apply_algebraMap, Real.log_pow]
  ring

noncomputable def fibreEquiv (Q : HeightOneSpectrum (𝓞 L)) :
    {v : FinitePlace K // below v = Q} ≃ Q.asIdeal.primesOver (𝓞 K) where
  toFun v := ⟨v.1.maximalIdeal.asIdeal, inferInstance, ⟨(congrArg HeightOneSpectrum.asIdeal v.2).symm⟩⟩
  invFun P := ⟨FinitePlace.mk ⟨P.1, P.2.1, ne_bot_of_liesOver_of_ne_bot Q.ne_bot P.1⟩, by
    ext1
    simp only [below, FinitePlace.maximalIdeal_mk]
    exact P.2.2.over.symm⟩
  left_inv v := Subtype.ext (FinitePlace.mk_maximalIdeal v.1)
  right_inv P := Subtype.ext (by simp only [FinitePlace.maximalIdeal_mk])

noncomputable instance (Q : HeightOneSpectrum (𝓞 L)) : Fintype {v : FinitePlace K // below v = Q} :=
  Fintype.ofEquiv _ (fibreEquiv Q).symm

theorem sum_fibre (Q : HeightOneSpectrum (𝓞 L)) :
    ∑ v : {v : FinitePlace K // below v = Q}, deg L v.1 = Module.finrank L K := by
  rw [← (fibreEquiv Q).symm.sum_comp, IsFractionRing.finrank_eq (𝓞 L) L (𝓞 K) K,
    ← sum_ramification_inertia_eq_finrank Q.asIdeal (𝓞 K)]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  simp only [deg, fibreEquiv, Equiv.coe_fn_symm_mk, FinitePlace.maximalIdeal_mk]

lemma finsum_fibre {α β : Type*} (π : α → β) [∀ b, Fintype {a // π a = b}] (n : α → ℕ) (N : ℕ)
    (g : β → ℝ) (hg : g.support.Finite) (hsum : ∀ b, ∑ a : {a // π a = b}, n a.1 = N) :
    ∑ᶠ a, (n a : ℝ) * g (π a) = N * ∑ᶠ b, g b := by
  classical
  have hfin : ∀ b, (π ⁻¹' {b}).Finite := fun b ↦
    Set.finite_coe_iff.mp (Finite.of_fintype {a // π a = b})
  have hA : (π ⁻¹' g.support).Finite := by
    rw [← Set.biUnion_preimage_singleton]
    exact hg.biUnion fun b _ ↦ hfin b
  rw [finsum_eq_sum_of_support_subset _ (s := hA.toFinset) ?_,
    finsum_eq_sum_of_support_subset _ (s := hg.toFinset) (by simp), Finset.mul_sum]
  · rw [← Finset.sum_fiberwise_of_maps_to (s := hA.toFinset) (t := hg.toFinset) (g := π)
      (fun a ha ↦ by simpa using ha)]
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    rw [Finset.sum_subtype (p := fun a ↦ π a = b) _ (fun a ↦ by
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage]
        exact ⟨And.right, fun h ↦ ⟨by rw [h]; simpa using hb, h⟩⟩)]
    have : ∀ a : {a // π a = b}, (n a.1 : ℝ) * g (π a.1) = n a.1 * g b := fun a ↦ by rw [a.2]
    rw [Fintype.sum_congr _ _ this, ← Finset.sum_mul, ← Nat.cast_sum, hsum]
  · intro a ha
    simp only [Set.Finite.coe_toFinset, Set.mem_preimage, Function.mem_support]
    exact right_ne_zero_of_mul ha

theorem proof : PlaceCentredSum.Statement := by
  intro L K _ _ _ _ _ O m t
  classical
  let g : HeightOneSpectrum (𝓞 L) → ℝ := fun Q ↦
    if AbsCentredAt O m (fun u ↦ FinitePlace.mk Q u) then -Real.log (FinitePlace.mk Q t) else 0
  have hL : ∑ᶠ w ∈ {w : FinitePlace L | AbsCentredAt O m fun u ↦ w u}, -Real.log (w t) =
      ∑ᶠ Q, g Q := by
    rw [finsum_mem_def, ← finsum_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finsum_congr fun Q ↦ ?_
    simp only [Set.indicator, Set.mem_ofPred_eq, g, FinitePlace.equivHeightOneSpectrum,
      Equiv.coe_fn_symm_mk]
    exact if_congr Iff.rfl rfl rfl
  have hK : ∑ᶠ v ∈ {v : FinitePlace K | AbsCentredAt O m fun u ↦ v (algebraMap L K u)},
      -Real.log (v (algebraMap L K t)) = ∑ᶠ v : FinitePlace K, (deg L v : ℝ) * g (below v) := by
    rw [finsum_mem_def]
    refine finsum_congr fun v ↦ ?_
    simp only [Set.indicator, Set.mem_ofPred_eq, g, centred_iff, neg_log_apply]
    split_ifs <;> simp
  have hg : g.support.Finite := by
    rcases eq_or_ne t 0 with rfl | ht
    · refine Set.finite_empty.subset fun Q hQ ↦ ?_
      simp [g] at hQ
    · refine ((FinitePlace.hasFiniteMulSupport ht).preimage
        (fun a _ b _ h ↦ FinitePlace.mk_eq_iff.mp h)).subset fun Q hQ ↦ ?_
      simp only [Function.mem_support, g] at hQ
      split_ifs at hQ
      · simp only [Set.mem_preimage, Function.mem_mulSupport]
        intro h1
        exact hQ (by simp [h1])
      · exact absurd rfl hQ
  rw [hK, hL]
  exact finsum_fibre below (deg L) _ g hg sum_fibre

end PlaceCentredSum

end GroundTheory.Heights₂.Heights

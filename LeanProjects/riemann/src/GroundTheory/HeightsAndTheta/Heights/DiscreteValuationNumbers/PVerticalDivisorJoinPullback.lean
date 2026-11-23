import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalDivisorJoinPullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section JoinPullback

variable {K K' : Type} {ι : K → Type} {ι' : K' → Type}

theorem joinCoords_inl {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (k : K)
    (i : ι k) : joinCoords y y' ⟨Sum.inl k, i⟩ = y ⟨k, i⟩ := rfl

theorem pointConeMap_joinCoords_joinForm {Ω : Type*} [Field Ω] (R : Type*) [CommRing R]
    [Algebra R Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    pointConeMap R (joinCoords y y') (joinForm f) =
      rename (Sum.inl : K → K ⊕ K') (pointConeMap R y f) := by
  simp only [pointConeMap, joinForm, aeval_rename]
  induction f using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    obtain ⟨k, i⟩ := v
    simp [hp, joinCoords_inl]

theorem joinForm_mem_pointIdeal_iff {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    joinForm f ∈ pointIdeal R (joinCoords y y') ↔ f ∈ pointIdeal R y := by
  simp only [pointIdeal, RingHom.mem_ker, pointConeMap_joinCoords_joinForm]
  exact map_eq_zero_iff _ (rename_injective _ Sum.inl_injective)

theorem isMultiHomog_joinForm [DecidableEq K] [DecidableEq K'] {R : Type*} [CommRing R]
    {f : MRing ι R} {bf : K → ℕ} (hf : IsMultiHomog f bf) :
    IsMultiHomog (joinForm (ι' := ι') f) (Sum.elim bf 0) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa [joinForm] using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [joinForm, map_add] using ihp.add ihq
  | monomial d r hr =>
    simp only [joinForm, rename_monomial]
    apply isWeightedHomogeneous_monomial
    subst hr
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]),
      Finsupp.weight_apply]
    funext s
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight]
    rcases s with k | k
    · simp [Pi.single_apply]
    · simp

end JoinPullback

theorem VerticalDivisorJoinPullback.proof : VerticalDivisorJoinPullback.Statement := by
  intro O _ _ _ ϖ Ω _ _ K _ _ ι _ K' _ _ ι' _ y y' b f g hD
  refine IsVerticalDivisor.of_unit_off_special ?_ ?_ ?_ ?_
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine ⟨Sum.elim bf 0, Sum.elim bg 0, isMultiHomog_joinForm hf, isMultiHomog_joinForm hg, ?_⟩
    funext s
    rcases s with k | k
    · simp [joinDeg, ← hb]
    · simp [joinDeg]
  · rw [joinForm_mem_pointIdeal_iff]; exact hD.num_not_mem
  · rw [joinForm_mem_pointIdeal_iff]; exact hD.den_not_mem
  · intro W hW hPW hrel hϖ
    let φ : MRing ι O →ₐ[O] MRing (Sum.elim ι ι') O :=
      rename (fun p : (Σ k, ι k) => (⟨Sum.inl p.1, p.2⟩ : Σ s : K ⊕ K', Sum.elim ι ι' s))
    have hφ : ∀ h, joinForm (ι' := ι') h = φ h := fun _ => rfl
    have hle : pointIdeal O y ≤ W.comap φ := by
      intro h hh
      rw [Ideal.mem_comap, ← hφ]
      exact hPW ((joinForm_mem_pointIdeal_iff O y y' h).mpr hh)
    have hrel' : IsRelevant (W.comap φ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel (Sum.inl k)
      exact ⟨i, by rw [Ideal.mem_comap]; simpa [φ, rename_X] using hi⟩
    have hϖ' : (C ϖ : MRing ι O) ∉ W.comap φ := by
      rw [Ideal.mem_comap]; simpa [φ, rename_C] using hϖ
    obtain ⟨u, v, hu, hv, huv⟩ :=
      hD.unit_off_special (W.comap φ) (Ideal.comap_isPrime φ W) hle hrel' hϖ'
    refine ⟨joinForm u, joinForm v, hu, hv, ?_⟩
    have := (joinForm_mem_pointIdeal_iff O y y' _).mpr huv
    simpa [hφ, map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR

import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaGood

theorem not_dvd_discr_of_inertia_fix (E N : Type) [Field E] [NumberField E] [Field N] [NumberField N]
    [Algebra E N] [IsGalois ℚ N] (q : ℕ) (hq : q.Prime)
    (h : ∀ Q : Ideal (𝓞 N), Q.IsMaximal → (q : 𝓞 N) ∈ Q → ∀ τ : N ≃ₐ[ℚ] N, (∀ x : 𝓞 N, τ • x - x ∈ Q) →
      ∀ y : E, τ (algebraMap E N y) = algebraMap E N y) : ¬ (q : ℤ) ∣ discr E := by
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  refine (not_dvd_discr_iff_forall_mem E (𝓞 E) hqz).2 fun P hP hqP => ?_
  have hqP' : (q : 𝓞 E) ∈ P := by simpa using hqP
  have hne : P ≠ ⊥ := fun h0 => by
    rw [h0, Ideal.mem_bot] at hqP'
    exact hq.ne_zero (Nat.cast_eq_zero.1 hqP')
  have hPm : P.IsMaximal := hP.isMaximal hne
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) P
  have hqQ : (q : 𝓞 N) ∈ Q := by
    have := (Ideal.mem_of_liesOver Q P _).1 hqP'
    rwa [map_natCast] at this
  have h1 := (GlobalTheory.UnramCompositum.ramificationIdx_eq_one_iff_fix ℚ E N Q).2 (h Q hQ hqQ)
  rw [← Ideal.over_def Q P] at h1
  have hu : Algebra.IsUnramifiedAt ℤ (P.under (𝓞 ℚ)) :=
    (not_dvd_discr_iff_forall_mem ℚ (𝓞 ℚ) hqz).1 (by
      rw [Rat.numberField_discr]; exact hqz.not_dvd_one) _ inferInstance (by
      rw [Ideal.under, Ideal.mem_comap, map_intCast]; exact hqP)
  have h2 : P.ramificationIdx ℤ = (P.under (𝓞 ℚ)).ramificationIdx ℤ * P.ramificationIdx (𝓞 ℚ) :=
    Ideal.ramificationIdx_tower (P.under (𝓞 ℚ)) P
  rw [h1, Ideal.ramificationIdx_eq_one (P.under (𝓞 ℚ)) ℤ, Nat.mul_one] at h2
  exact Ideal.ramificationIdx_eq_one_iff.1 h2

theorem exists_unramified_field_good : ∀ (N : IntermediateField ℚ ℂ) [NumberField N] [IsGalois ℚ N] (q : ℕ), q.Prime → ∀ Good : (ℂ ≃+* ℂ) → Prop, (∀ τ τ', Good τ → Good τ' → Good (τ.trans τ')) → (∀ (τ : ℂ ≃+* ℂ) (𝔮 : Ideal (𝓞 N)), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → Good τ) → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ ∀ τ : ℂ ≃+* ℂ, (∀ x ∈ F', τ x = x) → Good τ := by
  intro N _ _ q hq Good hmul hin
  have : Countable N := (Module.finBasis ℚ N).equivFun.injective.countable
  let T : Set (N ≃ₐ[ℚ] N) :=
    {σ | ∃ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal ∧ (q : 𝓞 N) ∈ 𝔮 ∧ σ ∈ 𝔮.inertia (N ≃ₐ[ℚ] N)}
  let S : (N ≃ₐ[ℚ] N) → Prop := fun σ => ∀ τ : ℂ ≃+* ℂ, (∀ x : N, τ (x : ℂ) = (σ x : ℂ)) → Good τ
  have hT : ∀ σ ∈ T, S σ := by
    rintro σ ⟨𝔮, h1, h2, h3⟩ τ hτ
    exact hin τ 𝔮 h1 h2 fun x => ⟨σ • x, (hτ x).symm, AddSubgroup.mem_inertia.1 h3 x⟩
  have h1 : (1 : N ≃ₐ[ℚ] N) ∈ T := by
    have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
    have : (Ideal.span {(q : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) (Ideal.span {(q : ℤ)})
    refine ⟨Q, hQ, ?_, one_mem _⟩
    have := (Ideal.mem_of_liesOver Q (Ideal.span {(q : ℤ)}) _).1 (Ideal.mem_span_singleton_self _)
    rwa [map_natCast] at this
  have hSmul : ∀ σ σ', S σ → S σ' → S (σ * σ') := by
    intro σ σ' hσ hσ' τ hτ
    obtain ⟨τ', hτ'⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq N (algebraMap N ℂ)
      ((algebraMap N ℂ).comp (σ' : N →+* N))
    have hτ'' : ∀ x : N, τ' (x : ℂ) = (σ' x : ℂ) := hτ'
    have g2 : Good (τ'.symm.trans τ) := hσ _ fun x => by
      have e : τ'.symm (x : ℂ) = (σ'.symm x : ℂ) := by
        rw [RingEquiv.symm_apply_eq, hτ'', AlgEquiv.apply_symm_apply]
      rw [RingEquiv.trans_apply, e, hτ, AlgEquiv.mul_apply, AlgEquiv.apply_symm_apply]
    have e : τ'.trans (τ'.symm.trans τ) = τ := RingEquiv.ext fun z => by simp
    exact e ▸ hmul _ _ (hσ' τ' hτ'') g2
  have hIS : ∀ σ ∈ Subgroup.closure T, S σ := fun σ hσ =>
    Subgroup.closure_induction'' (p := fun σ _ => S σ) hT
      (fun x ⟨𝔮, a, b, c⟩ => hT _ ⟨𝔮, a, b, inv_mem c⟩) (hT _ h1) (fun x y _ _ => hSmul x y) hσ
  let F₀ := IntermediateField.fixedField (Subgroup.closure T)
  have : NumberField (IntermediateField.lift F₀) :=
    have : FiniteDimensional ℚ (IntermediateField.lift F₀) :=
      (IntermediateField.liftAlgEquiv F₀).toLinearEquiv.finiteDimensional
    ⟨⟩
  refine ⟨IntermediateField.lift F₀, this, ?_, fun τ hτ => ?_⟩
  · rw [← discr_eq_discr_of_algEquiv F₀ (IntermediateField.liftAlgEquiv F₀)]
    exact not_dvd_discr_of_inertia_fix F₀ N q hq fun Q a b σ c y =>
      (IntermediateField.mem_fixedField_iff _ _).1 y.2 σ
        (Subgroup.subset_closure ⟨Q, a, b, AddSubgroup.mem_inertia.2 c⟩)
  · let τa : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := τ) fun x => by simp
    have hr : ∀ x : N, τ (x : ℂ) = (τa.restrictNormal N x : ℂ) := fun x =>
      (AlgEquiv.restrictNormal_commutes τa N x).symm
    refine hIS (τa.restrictNormal N) ?_ τ hr
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.closure T),
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact Subtype.ext ((hr x).symm.trans (hτ _ ((IntermediateField.mem_lift x).2 hx)))

end GlobalTheory.InertiaGood

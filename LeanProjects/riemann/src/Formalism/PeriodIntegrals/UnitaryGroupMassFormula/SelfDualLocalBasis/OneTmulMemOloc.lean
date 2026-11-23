import Mathlib
import Formalism.PeriodIntegrals.SelfDualLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.DualBasis

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.SelfDualLoc.W

open PI.SelfDualLoc

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_tmul (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) (r : R) :
    sigR σ R (e ⊗ₜ[F] r) = σ e ⊗ₜ[F] r := by
  rfl

theorem inclE_apply (R : Type) [CommRing R] [Algebra F R] (e : E) :
    inclE (F := F) R e = e ⊗ₜ[F] (1 : R) := by
  rfl

theorem sigR_inclE (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (e : E) :
    sigR σ R (inclE R e) = inclE R (σ e) := by
  rw [inclE_apply, inclE_apply, sigR_tmul]

variable [NumberField F] [NumberField E]

theorem intOE_map (σ : E →ₐ[F] E) {e : E} (he : e ∈ intOE E) : σ e ∈ intOE E := by
  obtain ⟨x, rfl⟩ := he
  refine ⟨⟨σ x, ?_⟩, rfl⟩
  have hx : IsIntegral ℤ (x : E) := NumberField.RingOfIntegers.isIntegral_coe x
  exact (mem_integralClosure_iff ℤ E).2 (hx.map (σ : E →+* E).toIntAlgHom)

theorem inclE_mem_Oloc (v : HeightOneSpectrum (𝓞 F)) {e : E} (he : e ∈ intOE E) :
    inclE (F := F) (v.adicCompletion F) e ∈ Oloc F E v := by
  rw [inclE_apply]
  exact Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)

theorem one_tmul_mem_Oloc (v : HeightOneSpectrum (𝓞 F)) {b : v.adicCompletion F}
    (hb : b ∈ v.adicCompletionIntegers F) : (1 : E) ⊗ₜ[F] b ∈ Oloc F E v := by
  exact Subring.subset_closure (Or.inr ⟨⟨b, hb⟩, rfl⟩)

theorem sigInt : SigInt := by
  intro F E _ _ _ _ _ σ v c hc
  have key : Oloc F E v ≤ (Oloc F E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show sigR σ _ (x ⊗ₜ[F] 1) ∈ Oloc F E v
      rw [sigR_tmul, ← inclE_apply]
      exact inclE_mem_Oloc v (intOE_map σ hx)
    · show sigR σ _ ((1 : E) ⊗ₜ[F] y) ∈ Oloc F E v
      rw [sigR_tmul, map_one]
      exact one_tmul_mem_Oloc v hy
  exact key hc

theorem unitLoc : UnitLoc := by
  intro F E _ _ _ _ _ v s hs
  have hs0 : (s : F) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact v.asIdeal.zero_mem
  set a : v.adicCompletion F := algebraMap F (v.adicCompletion F) (s : F) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact (map_ne_zero _).2 hs0
  have hval : Valued.v a = 1 := by
    have h1 : v.valuation F (algebraMap (𝓞 F) F s) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      refine le_antisymm (v.intValuation_le_one s) (not_lt.1 fun h => hs ?_)
      first
        | exact (v.intValuation_lt_one_iff_mem s).1 h
        | exact (Ideal.dvd_span_singleton).1 ((v.intValuation_lt_one_iff_dvd s).1 h)
    rw [ha, ← h1]
    first
      | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F s)
      | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (algebraMap (𝓞 F) F s)
      | rfl
  have hmem : a⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  refine ⟨(1 : E) ⊗ₜ[F] a⁻¹, one_tmul_mem_Oloc v hmem, ?_⟩
  rw [inclE_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def, mul_one, ← ha,
    mul_inv_cancel₀ ha0]
  rfl

end PI.SelfDualLoc.W

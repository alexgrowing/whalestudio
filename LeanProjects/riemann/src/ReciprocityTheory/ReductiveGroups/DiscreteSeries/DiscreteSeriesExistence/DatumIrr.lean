import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumInj

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

def jSm (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) : T.V →ₗ[ℂ] smD ε (rreg ε) where
  toFun v := ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_smooth hP v₀ v⟩
  map_add' v v' := Subtype.ext (datumEmbedding_add hP v₀ v v')
  map_smul' c v := Subtype.ext (datumEmbedding_smul hP v₀ c v)

theorem jSm_coe (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) :
    ((jSm hP v₀ v : smD ε (rreg ε)) : L2 ε) = uniformisationL2 ε Ψ v₀ v := rfl

theorem datumV_eq_range (hP : IsPsiFor ε lam T Ψ) (v₀ : T.V) :
    datumV ε Ψ v₀ = LinearMap.range (jSm hP v₀) := by
  ext x
  rw [mem_datumV_iff hP v₀ x, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, Subtype.ext hv.symm⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, rfl⟩

theorem smE_jSm (hP : IsPsiFor ε lam T Ψ) (v₀ v : T.V) {a b : Fin n} (hab : ε a = ε b) :
    smE ε (rreg ε) a b (jSm hP v₀ v) = jSm hP v₀ (T.dτ (Matrix.single a b 1) v) :=
  Subtype.ext (rightDerivative_datum_embedding hP v₀ v hab)

theorem jSm_injective (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    Function.Injective (jSm hP v₀) := by
  intro v v' h
  apply uniformisationL2_injective hP hv₀
  have := congrArg (fun x : smD ε (rreg ε) => (x : L2 ε)) h
  simpa [jSm_coe] using this

theorem datumV_isKIrrHW (hP : IsPsiFor ε lam T Ψ) {v₀ : T.V} (hv₀ : v₀ ≠ 0) :
    IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam) (datumV ε Ψ v₀) := by
  rw [datumV_eq_range hP v₀]
  refine ⟨LinearMap.finiteDimensional_range _, ?_, ?_, ?_⟩
  · rintro a b hab x ⟨v, rfl⟩
    exact ⟨T.dτ (Matrix.single a b 1) v, (smE_jSm hP v₀ v hab).symm⟩
  · intro S' hS' hst
    have hW : ∀ a b, ε a = ε b → ∀ v ∈ S'.comap (jSm hP v₀),
        T.dτ (Matrix.single a b 1) v ∈ S'.comap (jSm hP v₀) := by
      intro a b hab v hv
      rw [Submodule.mem_comap] at hv ⊢
      rw [← smE_jSm hP v₀ v hab]
      exact hst a b hab _ hv
    rcases HW.KType.dτ_irred T _ hW with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨v, rfl⟩ := hS' hx
      have hv : v ∈ S'.comap (jSm hP v₀) := hx
      rw [h, Submodule.mem_bot] at hv
      rw [hv, map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hS' ?_
      rintro x ⟨v, rfl⟩
      have hv : v ∈ S'.comap (jSm hP v₀) := by rw [h]; trivial
      exact hv
  · refine ⟨jSm hP v₀ T.w, ⟨T.w, rfl⟩, ?_, ?_, ?_⟩
    · intro h0
      apply HW.KType.w_ne_zero T
      apply jSm_injective hP hv₀
      rw [h0, map_zero]
    · intro a
      rw [smE_jSm hP v₀ T.w rfl, T.w_wt a, map_smul]
    · intro a b _ hab
      rw [smE_jSm hP v₀ T.w hab, T.w_hw a b ‹_› hab, map_zero]

end ReciprocityTheory.ChartRestriction.DS

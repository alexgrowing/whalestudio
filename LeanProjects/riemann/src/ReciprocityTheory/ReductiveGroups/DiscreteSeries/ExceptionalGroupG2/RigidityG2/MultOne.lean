import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

theorem rigid_multOne {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (j' : V →ₗ[ℂ] H) (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j' w = σ k (j' v))
    (hrange : ∀ v : V, j' v ∈ closGen E V)
    (horth : ∀ v v' : V, inner ℂ (j' v') ((v : D) : H) = 0) :
    j' = 0 := by
  apply LinearMap.ext
  intro v'
  have h0 : ∀ y ∈ closGen E V, inner ℂ (j' v') y = 0 := by
    intro y hy
    have hcl : IsClosed {y : H | inner ℂ (j' v') y = 0} :=
      isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hsub : ((genSub E V).map D.subtype : Set H) ⊆ {y | inner ℂ (j' v') y = 0} := by
      rintro _ ⟨y, hy, rfl⟩
      exact rigid_orth_genSub hgap hσ hD hV hc hVK j' hj horth v' y hy
    have hy' : y ∈ closure ((genSub E V).map D.subtype : Set H) := by
      rwa [← Submodule.topologicalClosure_coe]
    exact closure_minimal hsub hcl hy'
  rw [LinearMap.zero_apply]
  exact inner_self_eq_zero.1 (h0 _ (hrange v'))

end ReciprocityTheory.ChartRestriction.DS.G2

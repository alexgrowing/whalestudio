import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RigidOrth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.MultOneA

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def closGen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) : Submodule ℂ H :=
  ((genSub E V).map D.subtype).topologicalClosure

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
  ext v'
  have hort := rigid_orth hgap hσ hD hV hc hVK j' hj horth
  have hle : ((genSub E V).map D.subtype).topologicalClosure ≤
      (Submodule.span ℂ {j' v'})ᗮ := by
    apply generatedSub_closure_le hσ hD _ (Submodule.isClosed_orthogonal _)
    intro g hg v hv
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact hort g hg ⟨v, hv⟩ v'
  have hmem : j' v' ∈ (Submodule.span ℂ {j' v'})ᗮ := hle (hrange v')
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
  rw [LinearMap.zero_apply]
  exact inner_self_eq_zero.mp hmem

end ReciprocityTheory.ChartRestriction.DS

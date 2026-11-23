import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem rigid_orth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (j' : V →ₗ[ℂ] H) (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j' w = σ k (j' v))
    (horth : ∀ v v' : V, inner ℂ (j' v') ((v : D) : H) = 0) :
    ∀ g ∈ UJset ε, ∀ v v' : V, inner ℂ (j' v') (σ g ((v : D) : H)) = 0 := by
  intro g hg v v'
  have hC := rigid_orth_closure hgap hσ hD hV hc hVK j' hj horth v'
  apply hC
  obtain ⟨k, hk, Y, hY, rfl⟩ := polar_UJ hg
  have hVf : FiniteDimensional ℂ V := hV.1
  have hVK' : IsKStableSub ε E V := hV.2.1
  have hv : (v : D) ∈ genSub E V := by
    unfold genSub
    exact Submodule.mem_sInf.mpr fun T hT => hT.1 v.2
  have hkJ : kᴴ * Jm ε * k = Jm ε := by
    obtain ⟨hku, hkJ⟩ := hk
    have hu : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').mp hku
    rw [Matrix.mul_assoc, ← hkJ, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hkU : k ∈ UJset ε := hkJ
  have heU : NormedSpace.exp Y ∈ UJset ε := by
    have hg' : (k * NormedSpace.exp Y)ᴴ * Jm ε * (k * NormedSpace.exp Y) = Jm ε := hg
    rw [Matrix.conjTranspose_mul] at hg'
    show (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y = Jm ε
    calc (NormedSpace.exp Y)ᴴ * Jm ε * NormedSpace.exp Y
        = (NormedSpace.exp Y)ᴴ * (kᴴ * Jm ε * k) * NormedSpace.exp Y := by rw [hkJ]
      _ = ((NormedSpace.exp Y)ᴴ * kᴴ) * Jm ε * (k * NormedSpace.exp Y) := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := hg'
  rw [hσ.1.2 k hkU _ heU, ContinuousLinearMap.comp_apply]
  have h1 := exp_apply_mem_topologicalClosure hσ hD hVf hVK' hc hY hv
  obtain ⟨Z, hZ, hZk⟩ := exists_exp_eq_of_mem_Kset hk
  refine closure_mapsTo_of_genSub (σ k) (fun w hw => ?_) h1
  rw [← hZk]
  exact exp_inK_apply_mem_closure hσ hD hVf hVK' hZ hw

end ReciprocityTheory.ChartRestriction.DS

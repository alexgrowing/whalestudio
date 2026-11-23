import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.MultOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

theorem closGen_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) :
    ∀ g ∈ UJset ε, ∀ x ∈ closGen E V, σ g x ∈ closGen E V :=
  closure_genSub_stable hσ hD hV.1 hV.2.1 hc

theorem rigid_irred {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (S : Submodule ℂ H) (hS : S ≤ closGen E V) (hSc : IsClosed (S : Set H))
    (hSG : ∀ g ∈ UJset ε, ∀ x ∈ S, σ g x ∈ S) :
    S = ⊥ ∨ S = closGen E V := by
  classical
  have : CompleteSpace S := hSc.completeSpace_coe
  have : FiniteDimensional ℂ V := hV.1
  set VH : Submodule ℂ H := V.map D.subtype with hVH
  have : FiniteDimensional ℂ VH := inferInstance
  have : CompleteSpace VH := FiniteDimensional.complete ℂ VH
  have hSo : ∀ g ∈ UJset ε, ∀ x ∈ Sᗮ, σ g x ∈ Sᗮ := by
    intro g hg
    obtain ⟨g', hg', hgg⟩ := UnitaryGroupOfForm.inv_mem_UJ hg
    exact UnitaryGroupOfForm.orth_stable hσ hg hg' hgg S (hSG g' hg')
  have hVHK : ∀ k ∈ Kset ε, ∀ x ∈ VH, σ k x ∈ VH := by
    rintro k hk x ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hw'⟩ := hVK k hk v hv
    exact ⟨w, hw, hw'⟩
  have hVHo : ∀ k ∈ Kset ε, ∀ x ∈ VHᗮ, σ k x ∈ VHᗮ := by
    intro k hk
    obtain ⟨hk', hkk⟩ := UnitaryGroupOfForm.K_inv hk
    exact UnitaryGroupOfForm.orth_stable hσ (UnitaryGroupOfForm.K_mem_UJ hk) (UnitaryGroupOfForm.K_mem_UJ hk') hkk VH (hVHK _ hk')
  set S' : Submodule ℂ D := V ⊓ (Sᗮ).comap D.subtype with hS'
  have hS'K : IsKStableSub ε E S' := by
    intro a b hab v hv
    exact ⟨hV.2.1 a b hab v hv.1,
      UnitaryGroupOfForm.E_mem hD Sᗮ (Submodule.isClosed_orthogonal S) hSo a b v hv.2⟩
  rcases hV.2.2.1 S' inf_le_left hS'K with h0 | hV'
  · right
    refine le_antisymm hS (UnitaryGroupOfForm.closGen_le hD S hSc hSG V ?_)
    set P := S.starProjection with hP
    set Q := VH.starProjection with hQ
    let j' : V →ₗ[ℂ] H :=
      (((ContinuousLinearMap.id ℂ H - Q).comp P).toLinearMap).comp (D.subtype.comp V.subtype)
    have hj'v : ∀ v : V, j' v = P ((v : D) : H) - Q (P ((v : D) : H)) := fun v => rfl
    have hj'0 : j' = 0 := by
      refine rigid_multOne hgap hσ hD hV hc hVK j' ?_ ?_ ?_
      · intro k hk v w hvw
        have hkU := UnitaryGroupOfForm.K_mem_UJ hk
        rw [hj'v, hj'v, hvw, UnitaryGroupOfForm.proj_comm S (σ k) (hSG k hkU) (hSo k hkU),
          UnitaryGroupOfForm.proj_comm VH (σ k) (hVHK k hk) (hVHo k hk), map_sub]
      · intro v
        rw [hj'v]
        refine Submodule.sub_mem _ (hS (S.starProjection_apply_mem _)) ?_
        obtain ⟨y, hy, e⟩ := VH.starProjection_apply_mem (P ((v : D) : H))
        rw [← e]
        exact UnitaryGroupOfForm.mem_closGen V y hy
      · intro v v'
        rw [hj'v]
        exact Submodule.inner_left_of_mem_orthogonal (Submodule.mem_map_of_mem v.2)
          (VH.sub_starProjection_mem_orthogonal _)
    intro v hv
    have h1 : P (v : H) - Q (P (v : H)) = 0 := by
      rw [← hj'v ⟨v, hv⟩, hj'0]; rfl
    have h2 : P (v : H) ∈ VH := by
      rw [sub_eq_zero] at h1
      rw [h1]
      exact VH.starProjection_apply_mem _
    obtain ⟨y, hy, hyv⟩ := h2
    have hyv' : (y : H) = P (v : H) := hyv
    have hvy : v - y ∈ S' := by
      refine ⟨V.sub_mem hv hy, ?_⟩
      show ((v - y : D) : H) ∈ Sᗮ
      rw [Submodule.coe_sub, hyv']
      exact S.sub_starProjection_mem_orthogonal _
    rw [h0, Submodule.mem_bot, sub_eq_zero] at hvy
    rw [hvy, hyv']
    exact S.starProjection_apply_mem _
  · left
    have hle : closGen E V ≤ Sᗮ :=
      UnitaryGroupOfForm.closGen_le hD Sᗮ (Submodule.isClosed_orthogonal S) hSo V
        (fun v hv => (show v ∈ S' by rw [hV']; exact hv).2)
    rw [eq_bot_iff, ← Submodule.inf_orthogonal_eq_bot S]
    exact le_inf le_rfl (hS.trans hle)

end ReciprocityTheory.ChartRestriction.DS.G2

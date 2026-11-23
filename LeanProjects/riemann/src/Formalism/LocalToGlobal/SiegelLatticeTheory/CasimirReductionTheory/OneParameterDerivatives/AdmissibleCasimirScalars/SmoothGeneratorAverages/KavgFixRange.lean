import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace ExponentialDecomposition

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kavg_fix_range {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : IsKStableOn ε σ S)
    {e : KG ε → ℂ} (he : Continuous e) (hfix : ∀ x ∈ S, kavg hσ he x = x) (Θ : S →ₗ[ℂ] H)
    (hΘ : ∀ (a : KG ε) (v w : S), (w : H) = σ (toMK a) v → Θ w = σ (toMK a) (Θ v)) (s : S) :
    kavg hσ he (Θ s) = Θ s := by
  have hs : kavg hσ he (s : H) = s := hfix s s.2
  have hval : ∀ x : H, kavg hσ he x = ∫ k, e k • σ (toMK k) x ∂muK ε := fun x => by
    unfold Formalism.MainNotions.BridgeCPX.kavg
    rfl
  have hkS : ∀ k : KG ε, σ (toMK k) s ∈ S := fun k => hst _ k.2 _ s.2
  let F : KG ε → S := fun k => e k • ⟨σ (toMK k) s, hkS k⟩
  have hΘF : ∀ k, Θ (F k) = e k • σ (toMK k) (Θ s) := fun k => by
    simp only [F, map_smul]
    rw [hΘ k s ⟨σ (toMK k) s, hkS k⟩ rfl]
  have hsub : ((∫ k, F k ∂muK ε : S) : H) = ∫ k, (F k : H) ∂muK ε :=
    (S.subtypeₗᵢ.integral_comp_comm F).symm
  have hint : (∫ k, F k ∂muK ε) = s := by
    apply Subtype.ext
    rw [hsub, ← hs, hval]
    rfl
  rw [hval, integral_congr_ae (Filter.Eventually.of_forall fun k => (hΘF k).symm)]
  by_cases hFi : Integrable F (muK ε)
  · have h := (LinearMap.toContinuousLinearMap Θ).integral_comp_comm hFi
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    rw [h, hint]
  · rw [integral_undef hFi] at hint
    subst hint
    have h0 : ∀ k, F k = 0 := fun k => by
      ext
      simp [F]
    simp only [h0, map_zero, integral_zero]

theorem kavg_fix_isoK {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : IsKStableOn ε σ S)
    {e : KG ε → ℂ} (he : Continuous e) (hfix : ∀ x ∈ S, kavg hσ he x = x) {v : H} (hv : v ∈ isoK ε σ S) :
    kavg hσ he v = v := by
  have hle : isoK ε σ S ≤ LinearMap.ker
      ((((kavg hσ he : H →L[ℂ] H) - ContinuousLinearMap.id ℂ H : H →L[ℂ] H)) : H →ₗ[ℂ] H) := by
    refine sSup_le ?_
    rintro T ⟨Θ, hΘ, rfl⟩
    rintro x ⟨s, rfl⟩
    simp [LinearMap.mem_ker, sub_eq_zero, kavg_fix_range hσ hst he hfix Θ hΘ s]
  have h := hle hv
  simpa [LinearMap.mem_ker, sub_eq_zero] using h

end ExponentialDecomposition

theorem c0 : SmoothVectorsDense := by
  intro n ε H _ _ _ σ hσ hirr w hw S hfd hst v hv
  obtain ⟨e, he, hfix, hrange⟩ := compactProj (KG ε) (muK ε) H (fun k : KG ε => σ (toMK k)) hσ.1.1
    (fun a b => hσ.1.2 _ (umat_mem (a : UJ ε)) _ (umat_mem (b : UJ ε)))
    (fun a v => hσ.2.1 _ (umat_mem (a : UJ ε)) v)
    (fun v => (cont_orbit hσ v).comp continuous_subtype_val) S hfd (fun a v hv => hst _ a.2 v hv)
  have hfix' : ∀ x ∈ S, kavg hσ he x = x := fun x hx => by
    rw [kavg_apply]
    exact hfix x hx
  have hE : kavg hσ he v = v := ExponentialDecomposition.kavg_fix_isoK hσ hst he hfix' hv
  have hvc : v ∈ closure (Vsub ε hσ w : Set H) := by
    have h := Vsub_dense hσ hirr hw
    have h2 : v ∈ (Vsub ε hσ w).topologicalClosure := by
      rw [h]
      trivial
    exact h2
  have h3 : kavg hσ he v ∈ closure ((Vsub ε hσ w ⊓ isoK ε σ S : Submodule ℂ H) : Set H) := by
    refine map_mem_closure (kavg hσ he).continuous hvc ?_
    rintro _ ⟨Φ, hΦ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_inf]
    refine ⟨⟨kconv ε e Φ, test_kconv he hΦ, kavg_vec hσ w he hΦ⟩, ?_⟩
    rw [kavg_apply]
    exact hrange _
  rwa [hE] at h3

end Formalism.L2.SG.Pf.admitted

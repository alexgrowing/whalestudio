import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverageStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_equiv : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (G' : Type) [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [SecondCountableTopology G'] [T2Space G'] (Γ : AddSubgroup G) (Γ' : AddSubgroup G'), IsCoLat Γ → IsCoLat Γ' → ∀ e : G ≃ₜ+ G', (∀ x, e x ∈ Γ' ↔ x ∈ Γ) → ∀ Φ : G' → ℂ, Per Γ' Φ → avg Γ (fun x => Φ (e x)) = avg Γ' Φ := by
  intro G _ _ _ _ _ _ G' _ _ _ _ _ _ Γ Γ' hΓ hΓ' e he Φ hΦ
  letI mG : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI mG' : MeasurableSpace G' := borel G'
  haveI : BorelSpace G' := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  let f : G ≃ᵐ G' := e.toHomeomorph.toMeasurableEquiv
  haveI := hμ
  have hμ' : (μ.map f).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let eΓ : Γ' ≃ Γ :=
    { toFun := fun g => ⟨e.symm g, (he _).1 (by simpa using g.2)⟩
      invFun := fun x => ⟨e x, (he x).2 x.2⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hqmp : Measure.QuasiMeasurePreserving f.toEquiv.symm (μ.map f) μ :=
    MeasurePreserving.quasiMeasurePreserving ⟨f.symm.measurable, f.map_symm_map⟩
  have h𝓕' : IsAddFundamentalDomain Γ' (f '' 𝓕) (μ.map f) := by
    refine h𝓕.image_of_equiv f.toEquiv hqmp eΓ fun g x => ?_
    show e (e.symm (g : G') + x) = (g : G') + e x
    rw [map_add, ContinuousAddEquiv.apply_symm_apply]
  have hm : (μ.map f) (f '' 𝓕) = 1 := by
    rw [MeasurableEquiv.map_apply, Set.preimage_image_eq _ f.injective, h1]
  have hΦ' : Per Γ (fun x => Φ (e x)) :=
    ⟨hΦ.1.comp e.continuous, fun γ hγ x => by show Φ (e (γ + x)) = Φ (e x); rw [map_add]; exact hΦ.2 _ ((he γ).2 hγ) _⟩
  have A := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G' Γ' hΓ' (μ.map f) (f '' 𝓕) hμ' h𝓕' Φ hΦ).2.2.2
  have B := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ h𝓕 _ hΦ').2.2.2
  rw [hm] at A
  rw [h1] at B
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at A B
  rw [← A, ← B, f.measurableEmbedding.setIntegral_map, Set.preimage_image_eq _ f.injective]
  rfl

end GlobalTheory.CuspGeneric

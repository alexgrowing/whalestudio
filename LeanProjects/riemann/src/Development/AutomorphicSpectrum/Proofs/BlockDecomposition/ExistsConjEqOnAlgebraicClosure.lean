import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodExistenceCm
import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

noncomputable section

namespace GlobalTheory.CompanionTheory.EllipticCM

theorem exists_conj_eq_on_algebraicClosure {K : Type} [Field K] [Algebra K ℂ]
    (σ : ℂ ≃ₐ[K] ℂ) (ι : AlgebraicClosure K →ₐ[K] ℂ)
    (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hσ : ∀ x, σ (ι x) = ι (g x))
    (e : algebraicClosure K ℂ ≃ₐ[K] AlgebraicClosure K) :
    ∃ ρ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ,
      ∀ y : algebraicClosure K ℂ,
        (((ρ * ((e.trans g).trans e.symm) * ρ⁻¹) y : algebraicClosure K ℂ) : ℂ) = σ (y : ℂ) := by
  let ι' : algebraicClosure K ℂ →ₐ[K] ℂ := ι.comp (e : algebraicClosure K ℂ →ₐ[K] AlgebraicClosure K)
  have hmem : ∀ y, ι' y ∈ (algebraicClosure K ℂ).toSubalgebra := fun y =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic y).algHom ι')
  let ρ₀ : algebraicClosure K ℂ →ₐ[K] algebraicClosure K ℂ :=
    ι'.codRestrict (algebraicClosure K ℂ).toSubalgebra hmem
  let ρ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ :=
    AlgEquiv.ofBijective ρ₀ (Algebra.IsAlgebraic.algHom_bijective ρ₀)
  have hρ : ∀ w, ((ρ w : algebraicClosure K ℂ) : ℂ) = ι (e w) := fun _ => rfl
  refine ⟨ρ, fun y => ?_⟩
  obtain ⟨z, rfl⟩ := ρ.surjective y
  have h1 : (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) (ρ z) = ρ (e.symm (g (e z))) := by
    simp [AlgEquiv.mul_apply, AlgEquiv.aut_inv]
  rw [h1, hρ, hρ, hσ, AlgEquiv.apply_symm_apply]

theorem exists_globalArtinMap_tied : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ], Module.finrank ℚ K = 2 → ∃ Art₀ : Neutral.B1.IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, Neutral.B1.IsGlobalArtinMap K Art₀ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (s : Neutral.B1.Ideles K), GlobalTheory.EllipticCM.RestrictsTo σ (Art₀ (QuotientGroup.mk s)) → ∀ x : GroundTheory.LocalField.maximalAbelianExtension K (algebraicClosure K ℂ), ((GroundTheory.Global.artinMap K (algebraicClosure K ℂ) (GroundTheory.Global.IdeleClassGroup.mk K s) x : algebraicClosure K ℂ) : ℂ) = σ ((x : algebraicClosure K ℂ) : ℂ) := by
  intro K _ _ _ _ _
  let e : algebraicClosure K ℂ ≃ₐ[K] AlgebraicClosure K := IsAlgClosure.equiv K _ _
  obtain ⟨Art, hArt, hArtσ⟩ := GlobalTheory.LatVal.exists_globalArtinMap
    (CompanionTheory.FamInh.isGlobalArtin_inv (E := K) (Ω := algebraicClosure K ℂ)) e
  obtain ⟨φ, -, hφb, hφ⟩ := GlobalTheory.HeckeGal.exists_abMap_of_algEquiv e
  refine ⟨Art, hArt, ?_⟩
  rintro σ s ⟨ι, g, hσ, hg⟩ x
  obtain ⟨ρ, hρ⟩ := exists_conj_eq_on_algebraicClosure σ ι g hσ e
  obtain ⟨τ, hτ⟩ := GlobalTheory.HeckeGal.toAb_surjective (E := K) (Ω := algebraicClosure K ℂ)
    (CompanionTheory.FamInh.art0 K (algebraicClosure K ℂ) s)
  have h1 : Art (QuotientGroup.mk s) = Neutral.B1.toAb K ((e.symm.trans τ).trans e) :=
    hArtσ s τ (by rw [hτ, MonoidHom.inv_apply, inv_inv])
  have h2 : (e.symm.trans ((e.trans g).trans e.symm)).trans e = g := by
    ext y
    simp
  have h3 : GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) ((e.trans g).trans e.symm) =
      GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) τ :=
    hφb.1 (by rw [hφ, hφ, h2, hg, h1])
  have h4 : GlobalTheory.HeckeGal.toAb K (algebraicClosure K ℂ) (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) =
      CompanionTheory.FamInh.art0 K (algebraicClosure K ℂ) s := by
    rw [map_mul, map_mul, map_inv, h3, hτ, mul_comm (GlobalTheory.HeckeGal.toAb K _ ρ), mul_inv_cancel_right]
  have h5 := GroundTheory.LocalField.topologicalAbelianizationEquiv_mk_apply K (algebraicClosure K ℂ)
    (ρ * ((e.trans g).trans e.symm) * ρ⁻¹) x
  have h6 : GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)
      (((ρ * ((e.trans g).trans e.symm) * ρ⁻¹ : algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ)) :
        TopologicalAbelianization (algebraicClosure K ℂ ≃ₐ[K] algebraicClosure K ℂ)) =
      GroundTheory.Global.artinMap K (algebraicClosure K ℂ) (GroundTheory.Global.IdeleClassGroup.mk K s) := by
    refine Eq.trans (congrArg (GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)) h4) ?_
    exact (GroundTheory.LocalField.topologicalAbelianizationEquiv K (algebraicClosure K ℂ)).apply_symm_apply _
  rw [h6] at h5
  rw [h5, hρ]

end GlobalTheory.CompanionTheory.EllipticCM

end

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Unlinked
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportOfPrincipalSeriesSubquotient

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem val_unif (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (unif k : k) = uniformizer k := by
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact uniformizer_ne_zero hp.symm
  have h := Classical.epsilon_spec (p := fun p : kˣ => valuation k (p : k) < 1 ∧
    ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k))
    ⟨Units.mk0 p hp0, by rw [Units.val_mk0, hp]; exact uniformizer_lt_one,
      fun x hx => by rw [Units.val_mk0, hp]; exact le_uniformizer_iff.2 hx⟩
  exact le_antisymm (le_uniformizer_iff.2 h.1) (hp ▸ h.2 p (hp ▸ uniformizer_lt_one))

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SphUnl := by
  intro K _ _ _ n hn π v B hB
  obtain ⟨⟨s₀, hs₀⟩, huniq, htor, hunr, -⟩ := suppFacts K n hn π v
  refine ⟨(htor s₀ hs₀).1.2 fun y hy => ?_, fun s hs => ?_⟩
  · obtain ⟨μ, hμ, rfl⟩ := hunr s₀ B hs₀ hB y hy
    rfl
  · obtain ⟨σ, hσ, -⟩ := id hs
    obtain ⟨α, hα, hS⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π ((CG.hasSat_mk π v B).1 hB) hσ
    haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
    have h := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries (v.adicCompletion K) n (fun i => unrChar _ (α i))
      (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ (α i))) ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ hS.2.2
    have key : ∀ ξ ∈ chars s, ξ (unif _) ∈ B := by
      rintro ξ ⟨hξ, hm⟩
      rw [huniq s _ hs ⟨σ, hσ, h⟩] at hm
      obtain ⟨i, hi, e⟩ := Multiset.mem_map.1 hm
      rw [← IrrGL.ofChar_inj.1 e, unrChar_uniformizer _ _ (val_unif _), ← hα]
      exact Multiset.mem_map_of_mem _ hi
    intro ξ hξ ξ' hξ' _ e
    refine UpperTheory.ConvolutionTheory.Sph.unlinked K n hn π v B hB _ (key ξ hξ) _ (key ξ' hξ') ?_
    rw [← e, MonoidHom.mul_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel_right]

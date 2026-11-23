import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvertibleTopExteriorPower

theorem invertible_exteriorPower_top (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ)
    (hn : ∀ p, Module.rankAtStalk (R := R) M p = n) : Module.Invertible R (⋀[R]^n M) := by
  let s : Set R := {a | Module.Free (Localization.Away a) (LocalizedModule.Away a M)}
  have hs : Ideal.span s = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨a, ha, hfree⟩ := Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M m
      (fun m' _ => by rw [hn, hn])
    exact ha (hsm (Ideal.subset_span hfree))
  have hloc : ∀ r : s, IsLocalizedModule.Away r.1 (exteriorPowerMapOver (Localization.Away r.1) n
      (LocalizedModule.mkLinearMap (Submonoid.powers r.1) M)) := fun r =>
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r.1) (Localization.Away r.1) _).2
      (GlobalTheory.TopForm.isBaseChange_exteriorPower
        (LocalizedModule.isBaseChange (Submonoid.powers r.1) M) n)
  refine GlobalTheory.invertible_of_isLocalizedModule_span s hs (fun r => Localization.Away r.1)
    (fun r => ⋀[Localization.Away r.1]^n (LocalizedModule.Away r.1 M))
    (fun r => exteriorPowerMapOver (Localization.Away r.1) n
      (LocalizedModule.mkLinearMap (Submonoid.powers r.1) M)) fun r => ?_
  have hfree : Module.Free (Localization.Away r.1) (LocalizedModule.Away r.1 M) := r.2
  rcases subsingleton_or_nontrivial (Localization.Away r.1) with hB | hB
  · haveI : Subsingleton (⋀[Localization.Away r.1]^n (LocalizedModule.Away r.1 M)) :=
      Module.subsingleton (Localization.Away r.1) _
    exact Module.Invertible.congr (LinearEquiv.ofSubsingleton (Localization.Away r.1)
      (⋀[Localization.Away r.1]^n (LocalizedModule.Away r.1 M)))
  · obtain ⟨q⟩ : Nonempty (PrimeSpectrum (Localization.Away r.1)) := inferInstance
    have hfr : Module.finrank (Localization.Away r.1) (LocalizedModule.Away r.1 M) = n := by
      have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := Localization.Away r.1)
        (M := LocalizedModule.Away r.1 M)) q
      rw [Module.rankAtStalk_isBaseChange
        (LocalizedModule.isBaseChange (Submonoid.powers r.1) M), hn] at h1
      exact h1.symm
    let b := Module.finBasisOfFinrankEq (Localization.Away r.1) (LocalizedModule.Away r.1 M) hfr
    have hb := GlobalTheory.TopForm.isFreeGen_ιMulti b
    exact Module.Invertible.congr (LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ _) hb)

theorem invertible_alternatingMap_top : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ),
    (∀ p, Module.rankAtStalk (R := R) M p = n) → Module.Invertible R (M [⋀^Fin n]→ₗ[R] R) := by
  intro R _ M _ _ _ _ n hn
  haveI := invertible_exteriorPower_top R M n hn
  exact Module.Invertible.congr
    (exteriorPower.alternatingMapLinearEquiv (R := R) (M := M) (N := R) (n := n)).symm

end GlobalTheory.InvertibleTopExteriorPower

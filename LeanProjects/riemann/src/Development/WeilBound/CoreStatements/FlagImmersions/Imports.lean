import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifRiem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndAction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPeriodRiemannLattice

namespace RootFieldNumerics

open CategoryTheory NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem transport : Transport := by
  intro E _ _ _ H X t z g Λ _ _ R R' h A₀ x v hf hP hF
  obtain ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩ := hF
  have hs := SheetDecomposition.Riem.span_top R
  have hi := PeriodIso.isometry_of_periods R R' hs (LinearEquiv.refl _ _) h (fun a b => by rw [hf]; rfl) hP
  have hc := PeriodIso.commutes_of_periods R R' hs (LinearEquiv.refl _ _) h hP
  obtain ⟨u₂, χ₂, h1, h2, h3, h4⟩ := FibreAtPeriod.exists_reparam_isAH u h R'.Hm R.Hm χ hAH R.herm
    fun a b => (hi b a).symm
  refine ⟨A, inferInstance, φ, u₂, χ₂, hpb, h3, fun a p => ?_, SheetDecomposition.Riem.inj R, fun p => ?_, fun i => ?_⟩
  · rw [h1, h1, hc]
    exact hact a _
  · rw [h2, hmem]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, h.injective ((hP a).symm.trans ha)⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, hP a⟩
  · obtain ⟨v', e, d⟩ := hvec i
    exact ⟨v', e, h4 _ _ (by rwa [h.apply_symm_apply])⟩

end RootFieldNumerics

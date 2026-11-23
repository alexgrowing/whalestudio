import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NumberFieldStandardFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteDvrTorusExtensionSpecialFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeModelFiniteRingExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomAndIsAdicCompleteOfFiniteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem potModel_semiAbelian_torusExtension : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G ∧ Nonempty (TorusExtension (GlobalTheory.SS.spFibre G))) := by
  intro V K _ _ _ _ _ _ _ _ A _ hA
  obtain ⟨K', _, _, _, V', _, _, _, _, _, _, hfin, hinj, hcomm, G, _, hc, hsm, hsep, hqc, he, hT⟩ :=
    GlobalTheory.SS.semistableReduction_zero V K A hA
  obtain ⟨hloc, hcpl⟩ := GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr V V' hfin hinj
  haveI := hcpl
  have hA' : IsAbelianScheme (baseChange K K' A) := Out.TLinPf.isAb_pullback _ A hA
  have hG : IsSemiAbelian G :=
    GlobalTheory.SS.isSemiAbelian_of_abelian_generic_of_torusExt V' K' (baseChange K K' A) hA' G hc hsm hsep hqc he hT
  obtain ⟨V'', _, _, _, hcpl', _, hfin', hinj', hloc', hG', hT'⟩ :=
    GlobalTheory.exists_finite_dvr_torusExtension_specialFibre V' G hG
  obtain ⟨alg, hfd, hcomm', he'⟩ := GlobalTheory.SS.model_finite_ext V K A K' V' hcomm G he V'' hfin' hinj'
  let : Algebra V V'' := ((algebraMap V' V'').comp (algebraMap V V')).toAlgebra
  have : IsScalarTower V V' V'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfinV : Module.Finite V V'' := Module.Finite.trans V' V''
  have hlocV : IsLocalHom (algebraMap V V'') := by
    haveI := hloc; haveI := hloc'
    exact (inferInstance : IsLocalHom ((algebraMap V' V'').comp (algebraMap V V')))
  exact ⟨V'', FractionRing V'', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, alg, inferInstance, hcomm', hfinV, hlocV, hcpl', baseChange V' V'' G, inferInstance, he', hG', hT'⟩

end GlobalTheory.SS

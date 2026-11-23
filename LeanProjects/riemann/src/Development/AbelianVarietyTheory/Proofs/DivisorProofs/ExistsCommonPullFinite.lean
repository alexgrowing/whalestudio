import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibresCommonPullDegToFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCommonPullbackDegenerationDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackFractionFieldFiniteLocalExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegOfGenericFiniteNormalExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumRig.exists_common_pull_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ D' : DegPre W, Nonempty (IsPullDeg φ D₁.toPre D') → Nonempty (IsPullDeg φ D₂.toPre D') → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₃ : DegData R' (maximalIdeal R')), FinExt ρ ∧ Nonempty (IsPullDeg ρ D₁.toPre D₃.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₃.toPre) := by
  intro R _ _ _ hR D₁ D₂ W _ _ φ hφ D' ⟨h₁⟩ ⟨h₂⟩
  obtain ⟨E₁, E₂, L, _, β, E', ⟨e₁⟩, ⟨e₂⟩, ⟨f₁⟩, ⟨f₂⟩⟩ := GlobalTheory.T.exists_generic_fibres_common_pullDeg_to_field R hR D₁ D₂ W φ hφ D' h₁ h₂
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨K', _, io, E₃, hio, ⟨g₁⟩, ⟨g₂⟩⟩ := GlobalTheory.T.exists_finite_common_pullback_degenerationData (FractionRing R) L β E₁ E₂ E' f₁ f₂
  obtain ⟨R', _, _, _, ρ, E, hfin, hloc, ⟨k₁⟩, ⟨k₂⟩⟩ := GlobalTheory.T.exists_commonPullback_fractionField_finiteLocalExt R hR D₁.toPre D₂.toPre E₁ E₂ e₁ e₂ K' io E₃ hio g₁ g₂
  obtain ⟨D₃, ⟨p⟩⟩ := GlobalTheory.MumPull.exists_pull R R' ρ hfin.2.1 hloc D₁
  exact ⟨R', _, _, _, ρ, D₃, hfin, ⟨p⟩, GlobalTheory.T.isPullDeg_of_generic_finite_normal_extension R R' ρ hfin.1 hfin.2.1 D₁.toPre D₂.toPre D₃.toPre E p k₁ k₂⟩

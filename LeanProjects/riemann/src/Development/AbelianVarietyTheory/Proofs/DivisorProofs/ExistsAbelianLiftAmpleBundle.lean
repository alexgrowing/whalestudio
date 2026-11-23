import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfMumfordBundleLiftSqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPolarisationTrivialLiftsSqZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.SqStep.exists_lift : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (L : LB Y.left) (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ LBIso L₀ (L.pull i) := by
  intro R R₀ _ _ _ _ _ π hπ hsq Y₀ _ hY₀ L₀ hL₀ hamp hK
  obtain ⟨Y, _, i, l, Q, hY, hpb, hsqr, hQ, a₁, a₂, hQi⟩ :=
    GlobalTheory.T.exists_abelianScheme_lift_with_principal_lineBundle R R₀ π hπ hsq Y₀ hY₀ L₀ hL₀ hamp hK
  obtain ⟨L, hL, hLi⟩ := GlobalTheory.T.exists_lineBundle_lift_of_mumfordBundle_lift_sqZero R R₀ π hπ hsq Y₀ Y i l hY₀ hY hpb hsqr L₀ Q hL₀ hQ a₁ a₂ hQi
  haveI : Smooth Y.hom := hY.smooth
  have hamp' : RelAmple Y L :=
    GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ hsq Y Y₀ i hpb.1 inferInstance L L₀ hL hL₀ hLi hamp
  exact ⟨Y, inferInstance, L, i, hY, hL, hamp',
    GlobalTheory.T.kernelPolarisation_trivial_lifts_sqZero R R₀ π hπ hsq Y₀ Y i hY hpb L₀ L hL₀ hL hamp' hLi hK, hpb, hLi⟩

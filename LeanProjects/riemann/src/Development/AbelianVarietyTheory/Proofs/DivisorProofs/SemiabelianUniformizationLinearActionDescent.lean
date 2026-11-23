import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataUniformiseFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TqOfGtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtCompIsPullDeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationBaseChangeCompleteDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPulledBackFactorSamePolarisationStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TraitTwist

theorem exists_bundle_data_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → EvenOn P₉ → IsMonHom gen₉.hom → LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀))) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi R₉ _ _ _ ρ₉ G₉ _ _ β₉ β₉₂ P₉ A₉ gen₉ hfin₉ hpb₉ hsq₉ hG₉ hlam₉ hev₉ hgen₉ hgl₉
  have hR₉ : Base R₉ := ⟨hfin₉.1, by
    haveI := hR.2
    exact charZero_of_injective_ringHom hfin₉.2.1⟩
  obtain ⟨D₉', U₉, hL₉, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R₉ hR₉ G₉ P₉ hG₉ hev₉ A₉ gen₉ hgen₉ hgl₉
  obtain ⟨D₉, hD₉, hsame⟩ := GlobalTheory.T.uniformisation_pulledBackFactor_samePolarisation R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₉ ρ₉ G₉ β₉ β₉₂ P₉ hfin₉ hpb₉ hsq₉ hG₉ hlam₉ A₉ D₉' U₉ hL₉
  obtain ⟨R₀, _, _, _, ρ, D₀, G₀, _, _, β, β₂, A₀, U₀, hfin, hD₀, hpb, hsq, hlam⟩ :=
    GlobalTheory.T.samePolarisedData_uniformise_finite_extension R₉ hR₉ D₉ D₉' A₉ G₉ hG₉ U₉ hsame
  have hG₀ : IsSemiAbelian G₀ := GlobalTheory.SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hpb hG₉
  obtain ⟨P, hPL, hPE⟩ := GlobalTheory.Mum.unif_evenOn R₀ hfin.1 D₀ A₀ G₀ hG₀ U₀
  obtain ⟨hfin', hD'⟩ := GlobalTheory.Mum.FinExtComp.finExt_comp_isPullDeg R R₉ R₀ ρ₉ ρ D.toPre D₉.toPre D₀.toPre hfin₉ hfin hD₉ hD₀
  have hsp : spMap (ρ.comp ρ₉) = spMap ρ ≫ spMap ρ₉ := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  refine ⟨R₀, inferInstance, inferInstance, inferInstance, ρ.comp ρ₉, D₀, G₀, inferInstance, inferInstance, β ≫ β₉, β₂ ≫ β₉₂, P, A₀, U₀.gen,
    hfin', hD', ?_, GlobalTheory.ZM.SiegPull.isSquare_comp hsq hsq₉, hG₀, ?_, hPE, U₀.gen_hom, ?_, ?_⟩
  · rw [hsp]; exact IsGrpPullback.comp hpb hpb₉
  · rw [hPL]
    rw [← hL₉] at hlam₉
    have i₁ : (abelian₂ G₀ U₀.LG.L).IsLB := LB.isLB_linComb U₀.LG.isLB _ _
    have i₂ : ((abelian₂ G₉ U₉.LG.L).pull β₂).IsLB := pull_isLB (LB.isLB_linComb U₉.LG.isLB _ _) _
    have i₃ : ((abelian₂ G' U'.LG.L).pull ((β₂ ≫ β₉₂) ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)).IsLB :=
      pull_isLB (LB.isLB_linComb U'.LG.isLB _ _) _
    exact LBIso.trans i₁ i₂ i₃ hlam (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hlam₉ β₂ (Category.assoc _ _ _))
  · rw [hPL]; exact U₀.ext
  · intro W _ _ _ hW φ hφ hloc GW _ _ βW DW AW UW hpbW hLW
    rw [hPL] at hLW
    exact GlobalTheory.T.uniformization_base_change_complete_dvr R₀ hfin.1 D₀ A₀ G₀ hG₀ U₀ W hW φ hφ hloc GW βW DW AW UW hpbW hLW

end GlobalTheory.Mum.TraitTwist

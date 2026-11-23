import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUniformisationOfTraitUnifStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionTransferStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtCompIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem factor_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G₁ : Over (Sp R₁)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (U₁ : Unif (maximalIdeal R₁) D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G' U'.LG.L).pull (β₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  intro R _ _ _ hB D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  obtain ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, W, _, _, _, φ, GW, _, _, β, DW, AW, UW,
    hF₀, hD₀, hβ₀, hsq₀, hG₀, hW, hφi, hφl, hβ, hL, hDW, hLam⟩ :=
    GlobalTheory.T.semiabelian_uniformization_linear_action_transfer R hB D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  haveI := hB.2
  have hB₀ : Base R₀ := ⟨hF₀.1, charZero_of_injective_ringHom hF₀.2.1⟩
  obtain ⟨R₁, _, _, _, ρ₁, D₁, G₁, _, _, β₁, A₁, U₁, hF₁, hD₁, hβ₁, hL₁⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisation_of_trait_unif R₀ hB₀ D₀ G₀ P hG₀ W hW φ hφi hφl GW β DW AW UW hβ hL hDW
  obtain ⟨hF, hD⟩ := GlobalTheory.Mum.FinExtComp.finExt_comp_isPullDeg R R₀ R₁ ρ₀ ρ₁ D.toPre D₀.toPre D₁.toPre hF₀ hF₁ hD₀ hD₁
  obtain ⟨β₁₂, hsq₁, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (spMap ρ₁) G₀ G₁ β₁ hβ₁
  have hQ : (abelian₂ G' U'.LG.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U'.LG.isLB _ _
  have key := hlam P.L.L U₁.LG.L _ (abelian₂ G' U'.LG.L) _ P.L.isLB U₁.LG.isLB hQ hL₁ hLam
  have hsp : spMap (ρ₁.comp ρ₀) = spMap ρ₁ ≫ spMap ρ₀ := by
    simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁.comp ρ₀, D₁, G₁, inferInstance, inferInstance,
    β₁ ≫ β₀, β₁₂ ≫ β₀₂, A₁, U₁, hF, hD, ?_, ?_, ?_⟩
  · rw [hsp]; exact hβ₁.comp hβ₀
  · refine ⟨?_, ?_⟩
    · rw [Category.assoc, hsq₀.1, ← Category.assoc, hsq₁.1, Category.assoc]
    · rw [Category.assoc, hsq₀.2, ← Category.assoc, hsq₁.2, Category.assoc]
  · simpa only [Category.assoc] using key
end GlobalTheory.Mum

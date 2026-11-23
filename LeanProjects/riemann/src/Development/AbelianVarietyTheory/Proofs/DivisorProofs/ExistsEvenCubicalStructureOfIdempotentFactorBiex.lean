import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmBundleExtensionOnFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionIdempotentFactorTraitUnifStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfGenericPolarisationEStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_finExt_evenCP_of_factor_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ ∧ IsGrpPullback G₉ G (spMap ρ₉) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P₉ ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hOL G _ _ hG inc pr hinc hpr hip hpi R₁ _ _ _ ρ₁ G₁ _ _ β₁ β₁₂ A₁ gen₁ hρ₁ hβ₁ hsq₁ hgen₁ hE
  obtain ⟨R₂, _, _, _, ρ₂, D₂, D₂', F₂, A₂', G₂', _, _, U₂', oA₂, oG₂, G₂, _, _, inc₂, pr₂, β₂, β₂₂, A₂, gen₂, W, _, _, _,
    φ, GW, _, _, βW, DW, AW, UW, κ, hρ₂, hR₂, hG₂', hOL₂, hG₂, hinc₂, hpr₂, hip₂, hpi₂, hβ₂, hsq₂, hgen₂, hE₂, hPP₂,
    hW, hφ, hφl, hβW, hκ, hUW⟩ :=
    GlobalTheory.T.exists_finiteExtension_idempotentFactor_trait_unif R hR D D' F A' G' hG' U' oA oG hOL G hG inc pr hinc hpr hip hpi R₁ ρ₁ G₁ β₁ β₁₂ A₁ gen₁ hρ₁ hβ₁ hsq₁ hgen₁ hE
  obtain ⟨R₃, _, _, _, ρ₃, G₃, _, _, β₃, κ₃, L₃, hρ₃, hβ₃, hκ₃, hL₃, hL₃iso⟩ :=
    GlobalTheory.T.exists_finiteExtension_symmBundle_extension_on_factor R₂ hR₂ D₂ D₂' F₂ A₂' G₂' hG₂' U₂' oA₂ oG₂ hOL₂ G₂ hG₂ inc₂ pr₂ hinc₂ hpr₂ hip₂ hpi₂ A₂ gen₂ hgen₂ hE₂
      W hW φ hφ hφl GW βW DW AW UW κ hβW hκ hUW
  obtain ⟨R₉, _, _, _, ρ, G₉, _, _, β₉, β₉₂, P, A₉, gen₉, hρ, hβ₉, hsq₉, hG₉, hlam, hev, hgen₉, hiso₉⟩ :=
    GlobalTheory.T.exists_evenCubicalStructure_of_genericPolarisation_extension R₂ hR₂ G₂ hG₂ A₂ gen₂ hgen₂ _ hE₂ W φ GW βW DW AW UW κ hW hφ hφl hβW hκ hUW R₃ ρ₃ G₃ β₃ κ₃ L₃ hρ₃ hβ₃ hκ₃
      hL₃ hL₃iso
  have hΛ : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb U'.LG.isLB _ _
  have hΛ₂ : (abelian₂ G₂' U₂'.LG.L).IsLB := LB.isLB_linComb U₂'.LG.isLB _ _
  refine ⟨R₉, inferInstance, inferInstance, inferInstance, ρ.comp ρ₂, G₉, inferInstance, inferInstance, β₉ ≫ β₂,
    β₉₂ ≫ β₂₂, P, A₉, gen₉, ⟨hρ.1, hρ.2.1.comp hρ₂.2.1, hρ.2.2.comp hρ₂.2.2⟩, ?_, ?_, hG₉, ?_, hev, hgen₉, hiso₉⟩
  · rw [spMap_comp]
    exact hβ₉.comp hβ₂
  · exact ⟨by rw [Category.assoc, hsq₂.1, ← Category.assoc, hsq₉.1, Category.assoc],
      by rw [Category.assoc, hsq₂.2, ← Category.assoc, hsq₉.2, Category.assoc]⟩
  · have a := GlobalTheory.GenSpread.lbIso_pullback hPP₂ β₉₂
    have b := GlobalTheory.GenSpread.lbIso_pull_pull (pull_isLB hΛ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) β₉₂ (a' := β₉₂ ≫ β₂₂) rfl
    have c := GlobalTheory.GenSpread.lbIso_pull_pull hΛ (β₉₂ ≫ β₂₂)
      (a' := (β₉₂ ≫ β₂₂) ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) rfl
    have hL : (abelian₂ G₉ P.L.L).IsLB := LB.isLB_linComb P.L.isLB _ _
    refine LBIso.trans hL (pull_isLB (pull_isLB hΛ₂ _) _) (pull_isLB hΛ _) hlam ?_
    refine LBIso.trans (pull_isLB (pull_isLB hΛ₂ _) _) (pull_isLB (pull_isLB (pull_isLB hΛ _) _) _) (pull_isLB hΛ _) a ?_
    refine LBIso.trans (pull_isLB (pull_isLB (pull_isLB hΛ _) _) _) (pull_isLB (pull_isLB hΛ _) _) (pull_isLB hΛ _)
      (LBIso.symm b) (LBIso.symm c)

end GlobalTheory.Mum

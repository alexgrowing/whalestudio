import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointTranslatesInOpenSemiAbelianLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkNormalFlatOfSmoothOverRegularLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateBaseChangeOfPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionSqNonzeroLocusOfTranslateGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageTranslatesSeparatedGrpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGenericFibreInjectiveDomainMapStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.AmplePt

theorem exists_affine_nonzeroLocus_of_square : (∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G' : Over (Sp R')) [GrpObj G'], IsSemiAbelian G' → IsAbelianScheme ((Over.pullback (jK R')).obj G') → ∀ N : LB G'.left, N.IsLB → ∀ a : 𝟙_ (Over (Sp R')) ⟶ G', ∃ t : LB.Gen (LB.LinComb N (K := Fin 3) ![(𝟙 G' * (toUnit G' ≫ a)).left, (𝟙 G' * (toUnit G' ≫ a⁻¹)).left, 𝟙 G'.left] ![1, 1, -2]), t.IsGen) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (M₀ : LB G.left), M₀.IsLB → ∀ s₀ : M₀.Sec, IsAffineOpen (nonzeroLocus s₀) → (∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ (R' : Type) (_ : CommRing R') (ρ : R →+* R'), ρ.Flat ∧ ∃ x' : ↥(pullback G.hom (spMap ρ)), pullback.fst G.hom (spMap ρ) x' = y ∧ ∃ n, 1 ≤ n ∧ ∃ s : (lbPow (M₀.pull (pullback.fst G.hom (spMap ρ))) n).Sec, x' ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  intro H R _ _ _ G _ hG hab M₀ hM s₀ hV hy₀ y
  obtain ⟨z, hz1, hz2, hz3⟩ := GlobalTheory.T.exists_point_translates_in_open_semiAbelian_local R G hG (nonzeroLocus s₀) hy₀ y
  obtain ⟨hd, hn, hic, hfl, hinj⟩ := GlobalTheory.T.stalk_normal_flat_of_smooth_over_regular_local R G.left G.hom hG.smooth ((snd G G).left z)
  let R' : Type := G.left.presheaf.stalk ((snd G G).left z)
  let ρ : R →+* R' := (Spec.preimage (G.left.fromSpecStalk ((snd G G).left z) ≫ G.hom)).hom
  have hc : G.left.fromSpecStalk ((snd G G).left z) ≫ G.hom = spMap ρ := (Spec.map_preimage _).symm
  obtain ⟨a, Φ, hpb, hΦ1, hΦ2, hΦ3⟩ := GlobalTheory.T.exists_section_translate_baseChange_of_point R R' ρ G (G.left.fromSpecStalk ((snd G G).left z)) hc
  obtain ⟨x', hx'⟩ : ∃ x', Φ x' = z := by
    obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := (snd G G).left)
      (g := G.left.fromSpecStalk ((snd G G).left z)) z (closedPoint R') Scheme.fromSpecStalk_closedPoint.symm
    refine ⟨hpb.isoPullback.inv w, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw1]
  have e1 : pullback.fst G.hom (spMap ρ) x' = (fst G G).left z := by
    rw [← hΦ1, Scheme.Hom.comp_apply, hx']
  have e2 : ((𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a)).left ≫ pullback.fst G.hom (spMap ρ)) x' =
      (fst G G * snd G G).left z := by rw [hΦ2, Scheme.Hom.comp_apply, hx']
  have e3 : ((𝟙 ((Over.pullback (spMap ρ)).obj G) * (toUnit _ ≫ a⁻¹)).left ≫ pullback.fst G.hom (spMap ρ)) x' =
      (fst G G * (snd G G)⁻¹).left z := by rw [hΦ3, Scheme.Hom.comp_apply, hx']
  have hsemi' : IsSemiAbelian ((Over.pullback (spMap ρ)).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := hd; haveI := hn; haveI := hic
  have hab' := GlobalTheory.T.isAbelianScheme_genericFibre_injective_domain_map R R' ρ hinj G hab
  obtain ⟨t, ht⟩ := H R' ((Over.pullback (spMap ρ)).obj G) hsemi' hab'
    (M₀.pull (pullback.fst G.hom (spMap ρ))) (LB.isLB_pull hM _) a
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_sq_nonzeroLocus_of_translate_generator _ _ (pullback.fst G.hom (spMap ρ)) M₀ hM s₀ _ _ ⟨t, ht⟩
  haveI : IsAffineHom (pullback.fst G.hom (spMap ρ)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback G.hom (spMap ρ)).flip inferInstance
  have hW : IsAffineOpen (pullback.fst G.hom (spMap ρ) ⁻¹ᵁ nonzeroLocus s₀) := hV.preimage _
  have hL := GlobalTheory.T.isAffineOpen_preimage_translates_separated_grp R' ((Over.pullback (spMap ρ)).obj G) hsemi'.separated a _ hW
  refine ⟨R', inferInstance, ρ, hfl, x', e1.trans hz1, 2, by norm_num, s, ?_, ?_⟩
  · rw [hs]
    exact ⟨(Scheme.Hom.mem_preimage _).2 (e2 ▸ hz2), (Scheme.Hom.mem_preimage _).2 (e3 ▸ hz3)⟩
  · rw [hs, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]; exact hL

end GlobalTheory.AmplePt

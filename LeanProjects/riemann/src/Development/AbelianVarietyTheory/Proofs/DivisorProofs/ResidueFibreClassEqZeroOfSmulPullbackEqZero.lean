import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFstPreimageRestrictionBijectiveClosedImmersiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyClassPullbackReductionPairsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem isClosedImmersion_of_isPullback_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {q' : Y' ⟶ Sp R'} {χ : Y' ⟶ Y}
    (k : IsPullback χ q' q (spMap σ)) : IsClosedImmersion χ := by
  have : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hσ
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) k.flip this

theorem tmul_pull_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → CohomZeroIsConstants (OAff q') → ∀ (u : HO1 s₀) (y : HO1 s), TMul h₀.w t u y → pullHO1 w y = 0 → pullHO1 w₀ u = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ψ ψ' ψ₀ w w' w₀
    _hψ' hψ₀ hE _hs hq hC u y hT hy
  obtain ⟨hσ, hker, hσ₀, hker₀⟩ := hE
  haveI : IsClosedImmersion χ := isClosedImmersion_of_isPullback_surj hσ k
  haveI : IsClosedImmersion χ₀ := isClosedImmersion_of_isPullback_surj hσ₀ k₀
  haveI : IsClosedImmersion φ₀ := isClosedImmersion_of_isPullback_surj hσ₀ h₀
  have ht : σ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
  obtain ⟨f, c, hcf, hcy, hred⟩ := hT

  have h1 : (pairPull w).pull1 y = 0 := by
    have e := isPullO_pullHO1 w y
    unfold IsPullO at e
    rw [e, hy, map_zero]
  rw [← hcy, CoefMap.pullCohomologyOne_class, GlobalTheory.CatCoh.H1.mk_eq_zero] at h1
  obtain ⟨g, hg⟩ := h1
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : C1 (OPair ψ q), ∀ T T' (a : T ⟶ T'),
      f₁ T T' a = (pairPull w).α T' (f _ _ ((pairPull w).G.map a)) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hg' : ∀ (T T' : (Pair ψ)ᵒᵖ) (a : T ⟶ T'), g T' - mp (OPair ψ q) a (g T) = t • f₁ T T' a := by
    intro T T' a
    have e := congrFun (congrFun (congrFun hg T) T') a
    rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
    rw [e, hf₁, hcf, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, (pairPull w).smul, RingHom.id_apply]

  let gb : C0 (pairFst ψ ⋙ OPre χ q') := fun T ↦ preα χ q q' ((pairFst ψ).obj T) (g T)
  have hgb : d0 _ gb = 0 := by
    funext T T' a
    rw [amitsur_d0_apply]
    have nat : preα χ q q' _ (mp (OAff q) ((pairFst ψ).map a) (g T)) =
        mp (OPre χ q') ((pairFst ψ).map a) (preα χ q q' _ (g T)) := (preCoef k.w).naturality _ _
    change preα χ q q' _ (g T') - mp (OPre χ q') ((pairFst ψ).map a) (preα χ q q' _ (g T)) = 0
    rw [← nat]
    change preα χ q q' _ (g T') - preα χ q q' _ (mp (OPair ψ q) a (g T)) = 0
    have sm : ∀ U (r0 : R) b, preα χ q q' U (r0 • b) = σ r0 • preα χ q q' U b := (preCoef k.w).smul
    rw [← map_sub, hg', sm, ht, zero_smul]
  obtain ⟨r', hr', -⟩ := (GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion R' X Y Y' ψ χ q').2.2 hC gb hgb
  obtain ⟨r, rfl⟩ := hσ r'
  have hsec := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ⟨hσ, hker, hσ₀, hker₀⟩ hq
  have hex : ∀ T : (Pair ψ)ᵒᵖ, ∃ e, g T - algebraMap R _ r = t • e := by
    intro T
    refine ((hsec ((pairFst ψ).obj T)).2.1 _).1 ?_
    have e : preα χ q q' ((pairFst ψ).obj T) (algebraMap R ((OPair ψ q).obj T) r) =
        algebraMap R' ((pairFst ψ ⋙ OPre χ q').obj T) (σ r) :=
      SemiHom.map_algebraMap ((preCoef k.w).smul _) r
    rw [map_sub, e]
    exact sub_eq_zero.2 (hr' T)
  choose g₁ hg₁ using hex
  have hkill : ∀ (T T' : (Pair ψ)ᵒᵖ) (a : T ⟶ T'),
      t • (f₁ T T' a - (g₁ T' - mp (OPair ψ q) a (g₁ T))) = 0 := by
    intro T T' a
    rw [smul_sub, smul_sub, ← map_smul (mp (OPair ψ q) a), ← hg₁ T', ← hg₁ T, map_sub, AlgHom.commutes,
      ← hg' T T' a]
    abel

  obtain ⟨c₀, hc₀, hc₀'⟩ :=
    (GlobalTheory.T.cohomologyClass_pullback_reduction_pairs R R₀ σ₀ X X₀ Y Y₀ s s₀ q q₀ φ₀ χ₀ h₀.w ψ ψ₀ w w₀ hψ₀ inferInstance).1 f u hred
  have hz : (CoefMap.restrict (OAff q₀) (pairFst ψ ⋙ preAff χ₀)).pull1 (pullHO1 w₀ u) = 0 := by
    rw [← hc₀', GlobalTheory.CatCoh.H1.mk_eq_zero]
    refine ⟨fun T ↦ preα χ₀ q q₀ ((pairFst ψ).obj T) (g₁ T), ?_⟩
    funext T T' a
    rw [hc₀, amitsur_d0_apply, ← hf₁]
    have e1 := ((hsec ((pairFst ψ).obj T')).2.2.2 _).2 (hkill T T' a)
    rw [map_sub, map_sub, sub_eq_zero] at e1
    have nat : preα χ₀ q q₀ _ (mp (OAff q) ((pairFst ψ).map a) (g₁ T)) =
        mp (OPre χ₀ q₀) ((pairFst ψ).map a) (preα χ₀ q q₀ _ (g₁ T)) := (preCoef k₀.w).naturality _ _
    change _ - mp (OPre χ₀ q₀) ((pairFst ψ).map a) (preα χ₀ q q₀ _ (g₁ T)) = _
    rw [← nat]
    exact e1.symm
  exact (GlobalTheory.T.pairFst_preimage_restriction_bijective_closedImmersion R₀ X Y Y₀ ψ χ₀ q₀).1.1 (hz.trans (map_zero _).symm)

end GlobalTheory.AbCoh

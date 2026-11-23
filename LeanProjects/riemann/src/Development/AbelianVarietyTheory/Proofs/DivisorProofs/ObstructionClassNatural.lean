import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFstPreimageRestrictionBijectiveClosedImmersi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyClassPullbackReductionPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem isClosedImmersion_of_isPullback_spMap_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap σ)) : IsClosedImmersion φ := by
  have : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hσ
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip this

theorem restrict_pull1_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO1 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull1 ((preRes χ q').pull1 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 y := by
  obtain ⟨y, rfl⟩ := H1.mk_surjective _ y
  rfl

theorem restrict_pull2_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO2 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull2 ((preRes χ q').pull2 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 y := by
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ y
  rfl

set_option maxHeartbeats 1000000 in

theorem bock_natural : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → ∀ (x : HO1 s') (z : HO2 s₀) (z' : HO2 q₀), Bock h.w h₀.w t x z → Bock k.w k₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ψ ψ' ψ₀ w w' w₀ hc hc₀
    hS hs hq x z z' hB hB'
  obtain ⟨f, v, hfv, hf, hv⟩ := hB
  obtain ⟨f₂, v₂, hfv₂, hf₂, hv₂⟩ := hB'
  haveI : IsClosedImmersion φ := isClosedImmersion_of_isPullback_spMap_surj hS.1 h
  haveI : IsClosedImmersion φ₀ := isClosedImmersion_of_isPullback_spMap_surj hS.2.2.1 h₀
  haveI : IsClosedImmersion χ := isClosedImmersion_of_isPullback_spMap_surj hS.1 k
  haveI : IsClosedImmersion χ₀ := isClosedImmersion_of_isPullback_spMap_surj hS.2.2.1 k₀
  have hsec := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ hS hq
  obtain ⟨c₁, hc₁, hC₁⟩ :=
    (GlobalTheory.AbCoh.red_preimage_pairs R R' σ X X' Y Y' s s' q q' φ χ h.w ψ ψ' w w' hc inferInstance).1 f x hf
  obtain ⟨c₂, hc₂, hC₂⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R' Y Y' q q' σ χ k.w).1 f₂ (pullHO1 w' x)).1 hf₂
  obtain ⟨e₁, he₁, hE₁⟩ :=
    (GlobalTheory.AbCoh.red_preimage_pairs R R₀ σ₀ X X₀ Y Y₀ s s₀ q q₀ φ₀ χ₀ h₀.w ψ ψ₀ w w₀ hc₀ inferInstance).2 v z hv
  obtain ⟨e₂, he₂, hE₂⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ Y Y₀ q q₀ σ₀ χ₀ k₀.w).2.1 v₂ z').1 hv₂
  have nat : ∀ {U V : AffOp Y} (a : U ⟶ V) (b : (OAff q).obj U),
      preα χ q q' V (mp (OAff q) a b) = mp (OPre χ q') a (preα χ q q' U b) :=
    fun a b ↦ (preCoef k.w).naturality a b
  have nat₀ : ∀ {U V : AffOp Y} (a : U ⟶ V) (b : (OAff q).obj U),
      preα χ₀ q q₀ V (mp (OAff q) a b) = mp (OPre χ₀ q₀) a (preα χ₀ q q₀ U b) :=
    fun a b ↦ (preCoef k₀.w).naturality a b

  obtain ⟨g', hg'⟩ := (H1.mk_eq_mk (f := c₁)
    (f' := (CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂)).1 (by
      rw [hC₁, ← CoefMap.pullCohomologyOne_class, hC₂, restrict_pull1_preRes_pairFst])
  choose g hg using fun p : (Pair ψ)ᵒᵖ ↦ (hsec ((pairFst ψ).obj p)).1 (g' p)
  obtain ⟨F1, hF1⟩ : ∃ F1 : C1 (OPair ψ q), ∀ a b (u : a ⟶ b),
      F1 a b u = (pairPull w).α b (f _ _ ((pairPull w).G.map u)) := ⟨_, fun _ _ _ ↦ rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : C1 (OPair ψ q), ∀ a b (u : a ⟶ b),
      F2 a b u = f₂ _ _ ((pairFst ψ).map u) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hred : ∀ a b (u : a ⟶ b),
      preα χ q q' ((pairFst ψ).obj b) ((F1 - F2 - d0 (OPair ψ q) g) a b u) = 0 := by
    intro a b u
    have hc₂' : ((CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂).1 a b u =
        preα χ q q' ((pairFst ψ).obj b) (f₂ _ _ ((pairFst ψ).map u)) := hc₂ _ _ _
    have e : g' b - mp (pairFst ψ ⋙ OPre χ q') u (g' a) =
        c₁.1 a b u - ((CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂).1 a b u :=
      congrFun (congrFun (congrFun hg' a) b) u
    have e' : preα χ q q' ((pairFst ψ).obj b) (mp (OPair ψ q) u (g a)) =
        mp (pairFst ψ ⋙ OPre χ q') u (g' a) := by
      have := nat ((pairFst ψ).map u) (g a)
      rw [hg a] at this
      exact this
    simp only [Pi.sub_apply, amitsur_d0_apply, map_sub]
    rw [hF1, hF2, ← hc₁, ← hc₂', hg b, e', e, sub_self]
  choose u₀ hu₀ using fun a b (u : a ⟶ b) ↦ ((hsec ((pairFst ψ).obj b)).2.1 _).1 (hred a b u)
  have hD : F1 - F2 - d0 (OPair ψ q) g = t • (u₀ : C1 (OPair ψ q)) := by
    funext a b u; exact hu₀ a b u
  obtain ⟨W1, hW1⟩ : ∃ W1 : C2 (OPair ψ q), ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      W1 a b c u u' = (pairPull w).α c (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')) :=
    ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W2 : C2 (OPair ψ q), ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      W2 a b c u u' = v₂ _ _ _ ((pairFst ψ).map u) ((pairFst ψ).map u') := ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  have hdF1 : d1 (OPair ψ q) F1 = t • W1 := by
    funext a b c u u'
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hfv _) _) _)
      ((pairPull w).G.map u)) ((pairPull w).G.map u')
    simp only [d1_apply, Pi.smul_apply] at e ⊢
    rw [hF1, hF1, hF1, hW1, ← (pairPull w).naturality, Functor.map_comp, ← map_sub, ← map_add, e,
      (pairPull w).smul]
    rfl
  have hdF2 : d1 (OPair ψ q) F2 = t • W2 := by
    funext a b c u u'
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hfv₂ _) _) _)
      ((pairFst ψ).map u)) ((pairFst ψ).map u')
    simp only [d1_apply, Pi.smul_apply] at e ⊢
    rw [hF2, hF2, hF2, hW2, Functor.map_comp]
    exact e
  have hdd : d1 (OPair ψ q) (d0 (OPair ψ q) g) = 0 := by
    have := commAlgFunctorCoboundaryZero_mem_cocyclesOne (OPair ψ q) g
    rw [commAlgFunctorCocyclesOne_eq_ker] at this
    exact this
  have hmain : t • (W1 - W2 - d1 (OPair ψ q) u₀) = 0 := by
    rw [smul_sub, smul_sub, ← hdF1, ← hdF2, ← (d1 (OPair ψ q)).map_smul, ← hD, map_sub, map_sub, hdd,
      sub_zero, sub_self]
  have hzero : ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      preα χ₀ q q₀ ((pairFst ψ).obj c) ((W1 - W2 - d1 (OPair ψ q) u₀) a b c u u') = 0 := by
    intro a b c u u'
    refine ((hsec ((pairFst ψ).obj c)).2.2.2 _).2 ?_
    exact congrFun (congrFun (congrFun (congrFun (congrFun hmain a) b) c) u) u'
  obtain ⟨ub, hub⟩ : ∃ ub : C1 (pairFst ψ ⋙ OPre χ₀ q₀), ∀ a b (u : a ⟶ b),
      ub a b u = preα χ₀ q q₀ ((pairFst ψ).obj b) (u₀ a b u) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hH2 : H2.mk _ e₁ = H2.mk _ ((CoefMap.restrict (OPre χ₀ q₀) (pairFst ψ)).pullbackTwoCocycle e₂) := by
    refine H2.mk_eq_mk.2 ⟨ub, ?_⟩
    funext a b c u u'
    have E := hzero a b c u u'
    simp only [Pi.sub_apply, d1_apply, map_sub, map_add] at E
    have E1 : preα χ₀ q q₀ ((pairFst ψ).obj c) (mp (OPair ψ q) u' (u₀ a b u)) =
        mp (pairFst ψ ⋙ OPre χ₀ q₀) u' (ub a b u) := by
      rw [hub]; exact nat₀ ((pairFst ψ).map u') (u₀ a b u)
    have E2 : e₁.1 a b c u u' = preα χ₀ q q₀ _ (W1 a b c u u') := by rw [he₁, hW1]
    have E3 : ((CoefMap.restrict (OPre χ₀ q₀) (pairFst ψ)).pullbackTwoCocycle e₂).1 a b c u u' =
        preα χ₀ q q₀ _ (W2 a b c u u') := by
      rw [hW2]; exact he₂ _ _ _ _ _
    simp only [d1_apply, Pi.sub_apply]
    rw [E2, E3, ← E1, hub, hub]
    linear_combination -E
  rw [hE₁, ← CoefMap.pullCohomologyTwo_class, hE₂, restrict_pull2_preRes_pairFst] at hH2
  exact ((GlobalTheory.AbCoh.pair_pre_bijective R₀ X Y Y₀ ψ χ₀ q₀).2.1.1 hH2).symm

end GlobalTheory.AbCoh

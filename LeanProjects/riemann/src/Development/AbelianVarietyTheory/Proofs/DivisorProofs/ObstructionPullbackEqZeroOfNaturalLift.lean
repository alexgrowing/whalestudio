import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsCompStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem obstructionPullback_eq_zero_of_naturalLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (C'' : Type) [Category.{0} C''] (F'' : C'' ⥤ CommAlgCat.{0} R₀) (L'' : Pre I π F'') (m : CoefMap (RingHom.id R₀) F' F'') (u : ∀ T : C'', L'.B (m.G.obj T) →ₐ[R] L''.B T) (v : ∀ T : C'', L.B (n.G.obj (m.G.obj T)) →ₐ[R] L''.B T), L.IsLift L' n l → L'.IsLift L'' m u → L'.IsNat L'' m u → (∀ T b, L''.p T (v T b) = m.α T (n.α _ (L.p _ b))) → (∀ (T T' : C'') (a : T ⟶ T') b, L''.ρ a (v T b) = v T' (L.ρ (n.G.map (m.G.map a)) b)) → ∀ (w : Glob1 F) (c : GlobalTheory.CatCoh.H1 (ext R₁ F')), L.IsOb1 L' n l α w c → (extMap R₁ m).pull1 c = 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C' _ F' L L' n l C'' _ F'' L'' m u v hl hu hun hvp hvn w c hc
  obtain ⟨κ, σ', z, hκ, hσ', rfl, hz⟩ := hc
  choose σ'' hσ'' using fun T : C'' ↦ GlobalTheory.T.exists_augmentation_tensor_sigma_map R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T)
    (L''.semi T) (L''.surj T) (L''.ker T)

  have hdiff : ∀ (T : C'') (b : L.B (n.G.obj (m.G.obj T))),
      (u T).comp (l (m.G.obj T)) b - v T b ∈ I.map (algebraMap R (L''.B T)) := fun T b ↦ by
    refine (L''.ker T _).1 ?_
    rw [map_sub, sub_eq_zero]
    exact (hu T _).trans ((congrArg (m.α T) (hl _ b)).trans (hvp T b).symm)
  choose th hth using fun T : C'' ↦ ((theta_classify R R₀ (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T)))
    (L''.B T) I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _) ((u T).comp (l (m.G.obj T)))).1 (v T) (hdiff T)).exists

  have key : ∀ (T T' : C'') (a : T ⟶ T'),
      L''.ρ a (th T (w.1 (n.G.obj (m.G.obj T)))) =
        u T' (κ _ _ (m.G.map a) (w.1 (n.G.obj (m.G.obj T)))) + th T' (w.1 (n.G.obj (m.G.obj T'))) := by
    intro T T' a
    have h1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L'.B (m.G.obj T')) (L''.B T') _ _ _ (hκ _ _ (m.G.map a))).1 (u T')
    have h2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T'))) (F.obj (n.G.obj (m.G.obj T'))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L''.B T') (L''.B T') _ _ _ (hth T')).2 (L.ρ (n.G.map (m.G.map a)))
      (mp F (n.G.map (m.G.map a))) (fun x ↦ L.nat _ x)
    rw [AlgHom.comp_assoc] at h2
    have h3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk _ _ (L.p (n.G.obj (m.G.obj T))) (L.semi _) (L.surj _) (L.ker _)
      (L''.B T') _ _ _ _ _ h1).2.1 h2
    have h4 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj (m.G.obj T))) (F.obj (n.G.obj (m.G.obj T))) (L.p _)
      (L.semi _) (L.surj _) (L.ker _) (L''.B T) (L''.B T') _ _ _ (hth T)).1 (L''.ρ a)
    have e1 : (L''.ρ a).comp ((u T).comp (l (m.G.obj T))) =
        (u T').comp ((L'.ρ (m.G.map a)).comp (l (m.G.obj T))) := AlgHom.ext fun b ↦ hun a _
    have e2 : (L''.ρ a).comp (v T) = (v T').comp (L.ρ (n.G.map (m.G.map a))) := AlgHom.ext fun b ↦ hvn T T' a b
    rw [e1, e2] at h4
    have h5 := (GlobalTheory.T.isDifferenceDerivationOfLifts_add_swap_unique R R₀ I hI π hπ hk _ _ (L.p (n.G.obj (m.G.obj T))) (L.semi _) (L.surj _) (L.ker _)
      (L''.B T') _ _ ((v T').comp (L.ρ (n.G.map (m.G.map a)))) _ _ h4).2.2 |>.1 <| h3
    have h6 := DFunLike.congr_fun h5 (w.1 (n.G.obj (m.G.obj T)))
    rw [w.2 (n.G.map (m.G.map a))]
    exact h6
  choose g hgK hg using fun T : C'' ↦ (GlobalTheory.T.augmentation_sigma_map_basic_properties R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T)
    (L''.semi T) (L''.surj T) (L''.ker T) (σ'' T) (hσ'' T)).2.2.2 (-(th T (w.1 (n.G.obj (m.G.obj T)))))
    (neg_mem ((hth T).mem _))
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
  refine ⟨g, ?_⟩
  funext T T' a
  have sg := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L''.B T) (F''.obj T) (L''.p T) (L''.semi T) (L''.surj T)
    (L''.ker T) (L''.B T') (F''.obj T') (L''.p T') (L''.semi T') (L''.surj T') (L''.ker T') (L''.ρ a) (mp F'' a)
    (fun b ↦ L''.nat a b) (σ'' T) (σ'' T') (hσ'' T) (hσ'' T')
  have su := GlobalTheory.T.augmentation_sigma_map_natural R R₀ I hI π hπ hk R₁ α (L'.B (m.G.obj T')) (F'.obj (m.G.obj T')) (L'.p _) (L'.semi _)
    (L'.surj _) (L'.ker _) (L''.B T') (F''.obj T') (L''.p T') (L''.semi T') (L''.surj T') (L''.ker T') (u T')
    (coefHom m T') (fun b ↦ hu T' b) (σ' _) (σ'' T') (hσ' _) (hσ'' T')
  haveI : Algebra.Smooth R (L''.B T') := L''.smooth T'
  change g T' - extHom R₁ (mp F'' a) (g T) = extHom R₁ (coefHom m T') (z.1 _ _ (m.G.map a))
  refine sub_eq_zero.1 (GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α (L''.B T') (F''.obj T') (L''.p T') (L''.semi T')
    (L''.surj T') (L''.ker T') (σ'' T') (hσ'' T') _ ?_ ?_)
  · have k1 := hgK T'
    have k2 := sg.2 _ (hgK T)
    have k3 := su.2 _ (hz _ _ (m.G.map a)).1
    unfold Aug.KerQ at k1 k2 k3 ⊢
    rw [map_sub, map_sub, k1, k2, k3, sub_zero, sub_zero]
  · rw [map_sub, map_sub, hg T', ← sg.1, hg T, ← su.1, (hz _ _ _).2, map_neg, key T T' a]
    abel

end GlobalTheory.Obs

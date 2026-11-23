import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsAddSwapUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDifferenceDerivationOfLiftsCompStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem extHom_coefHom_restrict {R₀ : Type} [CommRing R₀] (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁]
    {C₂ C' : Type} [Category.{0} C₂] [Category.{0} C'] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (G : C' ⥤ C₂) (T : C')
    (y : R₁ ⊗[R₀] F₂.obj ((CoefMap.restrict F₂ G).G.obj T)) :
    extHom R₁ (coefHom (CoefMap.restrict F₂ G) T) y = y := by
  change Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (AlgHom.id R₀ _) y = y
  rw [Algebra.TensorProduct.map_id]; rfl

theorem isOb2_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (C₂ : Type) [Category.{0} C₂] (F₂ : C₂ ⥤ CommAlgCat.{0} R₀) (C' : Type) [Category.{0} C'] (G : C' ⥤ C₂) (n : CoefMap (RingHom.id R₀) F (G ⋙ F₂)) (L : Pre I π F) (L₂ : Pre I π F₂) (w : Glob1 F) (w₂ : Glob1 F₂) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)) (c₂ : GlobalTheory.CatCoh.H2 (ext R₁ F₂)), (∀ T, q1 n T (w.1 _) = w₂.1 (G.obj T)) → L.IsOb2 α w c → L₂.IsOb2 α w₂ c₂ → (extMap R₁ n).pull2 c = (extMap R₁ (CoefMap.restrict F₂ G)).pull2 c₂ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F C₂ _ F₂ C' _ G n L L₂ w w₂ c c₂ hw h1 h2
  obtain ⟨θ, σ, z, hθ, hσ, rfl, hz⟩ := h1
  obtain ⟨θ₂, σ₂, z₂, hθ₂, hσ₂, rfl, hz₂⟩ := h2
  have hl0 : ∀ T : C', ∃ l : L.B (n.G.obj T) →ₐ[R] L₂.B (G.obj T),
      ∀ b, L₂.p (G.obj T) (l b) = coefHom n T (L.p _ b) := by
    intro T
    haveI := L.smooth (n.G.obj T)
    exact homLift R R₀ I hI π hπ hk _ _ (L.p _) (L.semi _) (L.surj _) (L.ker _) _ _ (L₂.p (G.obj T))
      (L₂.semi _) (L₂.surj _) (L₂.ker _) (coefHom n T)
  choose l hl using hl0
  have hd : ∀ (T T' : C') (a : T ⟶ T') (b : L.B (n.G.obj T)),
      ((L₂.ρ (G.map a)).comp (l T)) b - ((l T').comp (L.ρ (n.G.map a))) b ∈
        I.map (algebraMap R (L₂.B (G.obj T'))) := by
    intro T T' a b
    refine (L₂.ker _ _).1 ?_
    rw [map_sub, sub_eq_zero]
    simp only [AlgHom.comp_apply]
    rw [L₂.nat, hl, hl, L.nat]
    exact (n.naturality a (L.p _ b)).symm
  choose κ hκ using fun (T T' : C') (a : T ⟶ T') ↦ ((theta_classify R R₀ (L.B (n.G.obj T)) (F.obj (n.G.obj T))
    (L₂.B (G.obj T')) I hI π hπ (L.p _) (L.semi _) (L.surj _) (L.ker _)
    ((L₂.ρ (G.map a)).comp (l T))).1 _ (hd T T' a)).exists
  have key : ∀ (T T' T'' : C') (a : T ⟶ T') (b : T' ⟶ T'') (ω : Ω[F.obj (n.G.obj T)⁄R₀]),
      θ₂ _ _ _ (G.map a) (G.map b) (q1 n T ω) + κ T T'' (a ≫ b) ω =
        L₂.ρ (G.map b) (κ T T' a ω) + κ T' T'' b (p1 F (n.G.map a) ω) +
          l T'' (θ _ _ _ (n.G.map a) (n.G.map b) ω) := by
    intro T T' T'' a b ω
    have e1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L₂.p (G.obj T)) (L₂.semi _) (L₂.surj _) (L₂.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hθ₂ _ _ _ (G.map a) (G.map b))).2
      (l T) (coefHom n T) (hl T)
    have e2 := hκ T T'' (a ≫ b)
    rw [Functor.map_comp, Functor.map_comp] at e2
    have s1 := (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
      e1).2.1 e2
    have f1 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T')) (L₂.B (G.obj T'')) _ _ _ (hκ T T' a)).1 (L₂.ρ (G.map b))
    have f2 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T')) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L₂.B (G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hκ T' T'' b)).2
      (L.ρ (n.G.map a)) (mp F (n.G.map a)) (L.nat (n.G.map a))
    have f3 := (GlobalTheory.T.isDifferenceDerivationOfLifts_comp R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _
      (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L.B (n.G.obj T'')) (L₂.B (G.obj T'')) _ _ _ (hθ _ _ _ (n.G.map a) (n.G.map b))).1 (l T'')
    have s2 := (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
      ((isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ _ _ _
        f1).2.1 f2)).2.1 f3
    have e := congrArg (fun t : Ω[F.obj (n.G.obj T)⁄R₀] →+ L₂.B (G.obj T'') ↦ t ω)
      ((isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) _ _ _ (l T'' |>.comp (L.ρ (n.G.map (a ≫ b)))) _ _
        s1).2.2.1 s2)
    exact e
  choose g hgK hg using fun (T T' : C') (a : T ⟶ T') ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _
    (L₂.p (G.obj T')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (σ₂ _) (hσ₂ _)).2.2.2 (κ T T' a (w.1 _))
    ((hκ T T' a).mem _)
  have kadd : ∀ {X : C₂} (y y' : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ y' → α.KerQ (y + y') :=
    fun y y' h h' ↦ by unfold Aug.KerQ at *; rw [map_add, h, h', add_zero]
  have kneg : ∀ {X : C₂} (y : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ (-y) :=
    fun y h ↦ by unfold Aug.KerQ at *; rw [map_neg, h, neg_zero]
  have ksub : ∀ {X : C₂} (y y' : R₁ ⊗[R₀] F₂.obj X), α.KerQ y → α.KerQ y' → α.KerQ (y - y') :=
    fun y y' h h' ↦ by rw [sub_eq_add_neg]; exact kadd _ _ h (kneg _ h')
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
  refine ⟨fun T T' a ↦ -g T T' a, ?_⟩
  funext T T' T'' a b
  haveI := L₂.smooth (G.obj T'')
  have nb := sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L₂.p (G.obj T')) (L₂.semi _) (L₂.surj _) (L₂.ker _) _ _
    (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (L₂.ρ (G.map b)) (mp F₂ (G.map b)) (L₂.nat (G.map b))
    (σ₂ _) (σ₂ _) (hσ₂ _) (hσ₂ _)
  have nl := sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L.p (n.G.obj T'')) (L.semi _) (L.surj _) (L.ker _) _ _
    (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _) (l T'') (coefHom n T'') (hl T'')
    (σ _) (σ₂ _) (hσ _) (hσ₂ _)
  change extHom R₁ (mp F₂ (G.map b)) (-g T T' a) - -g T T'' (a ≫ b) + -g T' T'' b =
    extHom R₁ (coefHom n T'') (z.1 _ _ _ (n.G.map a) (n.G.map b)) -
      extHom R₁ (coefHom (CoefMap.restrict F₂ G) T'') (z₂.1 _ _ _ (G.map a) (G.map b))
  rw [extHom_coefHom_restrict, ← sub_eq_zero]
  refine GlobalTheory.T.augmentation_sigma_map_injective_of_flat R R₀ I hI π hπ hk R₁ α _ _ (L₂.p (G.obj T'')) (L₂.semi _) (L₂.surj _) (L₂.ker _)
    (σ₂ _) (hσ₂ _) _ ?_ ?_
  · refine ksub _ _ (kadd _ _ (ksub _ _ ?_ (kneg _ (hgK _ _ _))) (kneg _ (hgK _ _ _)))
      (ksub _ _ (nl.2 _ (hz _ _ _ _ _).1) (hz₂ _ _ _ _ _).1)
    rw [map_neg]; exact kneg _ (nb.2 _ (hgK _ _ _))
  · change σ₂ (G.obj T'') ((_ : R₁ ⊗[R₀] F₂.obj (G.obj T'')) -
      (_ - z₂.1 (G.obj T) (G.obj T') (G.obj T'') (G.map a) (G.map b))) = 0
    simp only [map_sub, map_add, map_neg]
    rw [← nb.1, ← nl.1, hg, hg, hg, (hz _ _ _ _ _).2, (hz₂ _ _ _ _ _).2, ← hw, w.2 (n.G.map a)]
    linear_combination key T T' T'' a b (w.1 _)

end GlobalTheory.Obs

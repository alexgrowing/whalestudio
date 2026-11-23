import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem Trait.exists_fibre_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f ∧ f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left ∧ f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
  intro R _ _ _ _ D C W _ _ _ T F _ _ _ hF

  have hρ : Function.Injective ((algebraMap (FractionRing W) F).comp ((algebraMap W (FractionRing W)).comp T.φ)) :=
    (algebraMap (FractionRing W) F).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp T.inj)
  obtain ⟨ga, hga, hy⟩ := Modif.factor_gp R C.toModif F _ (jFK (R := W) F ≫ jK W ≫ T.ξ) hρ (by
    rw [Category.assoc, Category.assoc, T.ξ_π]
    simp only [jK, jFK, spMap, ← Spec.map_comp]
    rfl)
  have hga' : ga = algebraMap (FractionRing R) F :=
    IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (hga r).trans (hF r).symm)
  subst hga'
  have hu : jFK (R := W) F ≫ jK W ≫ T.ξ = jFK (R := R) F ≫ C.gp := hy

  have s₁ : IsPullback (pullback.snd (jFK (R := W) F) T.A.A.hom) (pullback.fst (jFK (R := W) F) T.A.A.hom)
      T.A.A.hom (jFK (R := W) F) := (IsPullback.of_hasPullback _ _).flip
  haveI : IsIso T.U.gen.inv.left := ⟨⟨T.U.gen.hom.left, by rw [← Over.comp_left, T.U.gen.inv_hom_id, Over.id_left],
    by rw [← Over.comp_left, T.U.gen.hom_inv_id, Over.id_left]⟩⟩
  have s₂ : IsPullback T.U.gen.inv.left T.A.A.hom (pullback.snd T.G.hom (jK W)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact Over.w T.U.gen.inv⟩
  have s₃ : IsPullback (pullback.fst T.G.hom (jK W)) (pullback.snd T.G.hom (jK W)) T.G.hom (jK W) :=
    IsPullback.of_hasPullback _ _
  have hW : IsPullback ((pullback.snd (jFK (R := W) F) T.A.A.hom) ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β)
      (pullback.fst (jFK (R := W) F) T.A.A.hom) C.G.hom (jFK (R := R) F ≫ C.gp) := by
    have := ((s₁.paste_horiz s₂).paste_horiz s₃).paste_horiz T.cart.1
    rw [← hu]
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using this

  have t₁ : IsPullback (pullback.snd (jFK (R := R) F) C.A.A.hom) (pullback.fst (jFK (R := R) F) C.A.A.hom)
      C.A.A.hom (jFK (R := R) F) := (IsPullback.of_hasPullback _ _).flip
  have hR : IsPullback (pullback.snd (jFK (R := R) F) C.A.A.hom ≫ C.α) (pullback.fst (jFK (R := R) F) C.A.A.hom)
      C.G.hom (jFK (R := R) F ≫ C.gp) := t₁.paste_horiz C.α_cart.1
  refine ⟨(hW.isoIsPullback _ _ hR).hom, inferInstance, hW.isoIsPullback_hom_snd _ _ hR, ?_⟩
  exact hW.isoIsPullback_hom_fst _ _ hR

end GlobalTheory.Mum

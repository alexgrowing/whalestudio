import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTripleOfAbelianModelDedekind
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveSpMapOfDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFractionFieldIsPullbackOfUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescOfFlatOfSchemeTheoreticallyDominantBasStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GoodDescW
set_option autoImplicit false

section Sq2
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}

noncomputable def sq2 (w : φ ≫ G.hom = G'.hom ≫ f) : (G' ⊗ G').left ⟶ (G ⊗ G).left :=
  (lift (pushPt w (fst G' G')) (pushPt w (snd G' G'))).left

theorem grpSchemeSquareProductMap_comp_fst (w : φ ≫ G.hom = G'.hom ≫ f) : sq2 w ≫ (fst G G).left = (fst G' G').left ≫ φ := by
  rw [sq2, ← Over.comp_left, lift_fst]; rfl

theorem grpSchemeSquareProductMap_comp_snd (w : φ ≫ G.hom = G'.hom ≫ f) : sq2 w ≫ (snd G G).left = (snd G' G').left ≫ φ := by
  rw [sq2, ← Over.comp_left, lift_snd]; rfl

theorem grpSchemeSquareProductMap_eq_tensorHom (w : φ ≫ G.hom = G'.hom ≫ f) {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} (h : IsSquare φ φ₂) :
    φ₂ = sq2 w :=
  Over.tensorObj_ext _ _ (h.1.trans (grpSchemeSquareProductMap_comp_fst w).symm) (h.2.trans (grpSchemeSquareProductMap_comp_snd w).symm)

theorem isPullback_squareMapOfCompatibleMorphism (w : φ ≫ G.hom = G'.hom ≫ f) (h : IsPullback φ G'.hom G.hom f) :
    IsPullback (sq2 w) (G' ⊗ G').hom (G ⊗ G).hom f :=
  CM.TripleModel.isPullback_tensor h h (grpSchemeSquareProductMap_comp_fst w) (grpSchemeSquareProductMap_comp_snd w)

theorem grpSchemeSquareProductMap_comp {T V : Scheme.{0}} {t : S' ⟶ T} {u : T ⟶ V} {v : S ⟶ V} {H : Over T} {X : Over V}
    {ψ : G'.left ⟶ H.left} {α : H.left ⟶ X.left} {β : G.left ⟶ X.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) (w₁ : ψ ≫ H.hom = G'.hom ≫ t) (w₂ : α ≫ X.hom = H.hom ≫ u)
    (w₃ : β ≫ X.hom = G.hom ≫ v) (h : ψ ≫ α = φ ≫ β) : sq2 w₁ ≫ sq2 w₂ = sq2 w ≫ sq2 w₃ := by
  apply Over.tensorObj_ext
  · change sq2 w₁ ≫ sq2 w₂ ≫ (fst X X).left = sq2 w ≫ sq2 w₃ ≫ (fst X X).left
    rw [grpSchemeSquareProductMap_comp_fst, grpSchemeSquareProductMap_comp_fst, ← Category.assoc, grpSchemeSquareProductMap_comp_fst, ← Category.assoc, grpSchemeSquareProductMap_comp_fst,
      Category.assoc, Category.assoc, h]
  · change sq2 w₁ ≫ sq2 w₂ ≫ (snd X X).left = sq2 w ≫ sq2 w₃ ≫ (snd X X).left
    rw [grpSchemeSquareProductMap_comp_snd, grpSchemeSquareProductMap_comp_snd, ← Category.assoc, grpSchemeSquareProductMap_comp_snd, ← Category.assoc, grpSchemeSquareProductMap_comp_snd,
      Category.assoc, Category.assoc, h]
end Sq2

section Sq
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem mul_sq (h : IsGrpPullback G' G f φ) (φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left)
    (h₁ : φ₂ ≫ (fst G G).left = (fst G' G').left ≫ φ) (h₂ : φ₂ ≫ (snd G G).left = (snd G' G').left ≫ φ) :
    φ₂ ≫ μ[G].left = μ[G'].left ≫ φ := by
  have e := h.2 _ (fst G' G') (snd G' G') (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) rfl rfl
  have e' : (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G'))).left = φ₂ :=
    Over.tensorObj_ext _ _
      (by change (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ fst G G).left = φ₂ ≫ (fst G G).left
          rw [lift_fst]; exact h₁.symm)
      (by change (lift (pushPt h.1.w (fst G' G')) (pushPt h.1.w (snd G' G')) ≫ snd G G).left = φ₂ ≫ (snd G G).left
          rw [lift_snd]; exact h₂.symm)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, Over.comp_left, e'] at e
  exact e

theorem inv_sq (h : IsGrpPullback G' G f φ) : φ ≫ ι[G].left = ι[G'].left ≫ φ := by
  have e : (pushPt h.1.w ((𝟙 G')⁻¹)).left = ((pushPt h.1.w (𝟙 G'))⁻¹).left :=
    congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  rw [Hom.inv_def, Hom.inv_def, Over.comp_left] at e
  change (𝟙 G' ≫ ι[G']).left ≫ φ = (𝟙 G'.left ≫ φ) ≫ ι[G].left at e
  simpa using e.symm

theorem one_sq (h : IsGrpPullback G' G f φ) : f ≫ η[G].left = η[G'].left ≫ φ := by
  have e : (pushPt h.1.w (1 : 𝟙_ (Over S') ⟶ G')).left = (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  rw [Hom.one_def, Hom.one_def, Over.comp_left] at e
  change (toUnit (𝟙_ (Over S')) ≫ η[G']).left ≫ φ = _ at e
  simp only [Over.comp_left, Over.toUnit_left] at e
  simpa using e.symm
end Sq

theorem hasGoodReduction_of_model : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∀ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) → IsPullback g G.hom X.hom (spMap (algebraMap R W)) → e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g → HasGoodReduction R K A := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax A _ _ hA G _ hG eI he X a g ha hg hcomp
  have : IsMonHom eI.hom := he
  obtain ⟨hfl, hsu⟩ := GlobalTheory.T.flat_surjective_spMap_of_dvr_alt R K W K' hmax
  have hsq := GlobalTheory.T.spec_fraction_field_isPullback_of_unramified_alt R K W K' hmax
  have : QuasiCompact (spMap (algebraMap R W)) := inferInstance
  have : QuasiCompact (spMap (algebraMap R K)) := inferInstance
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) := schemeTheoreticallyDominant_fractionField R K
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have hj : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap (algebraMap R W)) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hXs : Smooth X.hom := MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) hg.flip hj hG.smooth
  have hXp : IsProper X.hom := GrpFlatDesc.isProper_of_isPullback hg
  have hXc : GeometricallyConnected X.hom := GrpFlatDesc.geometricallyConnected_of_isPullback hg
  have hX2 : Flat (X ⊗ X).hom := inferInstanceAs (Flat (pullback.fst X.hom X.hom ≫ X.hom))

  have hρ : IsGrpPullback ((Over.pullback (spMap (algebraMap W K'))).obj G) G (spMap (algebraMap W K')) (pullback.fst G.hom (spMap (algebraMap W K'))) := isGrpPullback_pullback G (spMap (algebraMap W K'))
  have hψ : IsGrpPullback ((Over.pullback (spMap (algebraMap W K'))).obj G) A (spMap (algebraMap K K')) (eI.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) :=
    ((isGrpPullback_of_iso eI).comp (isGrpPullback_pullback A (spMap (algebraMap K K')))).congr (Category.id_comp _) rfl
  have hc : (eI.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
    rw [Category.assoc]; exact hcomp

  obtain ⟨hm, hm1, hm2, hm3⟩ := GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base (spMap (algebraMap R W)) (spMap (algebraMap R K)) (spMap (algebraMap K K')) (spMap (algebraMap W K')) hsq X.hom (X ⊗ X).hom (G ⊗ G).hom (sq2 hg.w)
    (isPullback_squareMapOfCompatibleMorphism hg.w hg) (A ⊗ A).hom (sq2 ha.w) (isPullback_squareMapOfCompatibleMorphism ha.w ha)
    ((Over.pullback (spMap (algebraMap W K'))).obj G ⊗ (Over.pullback (spMap (algebraMap W K'))).obj G).hom (sq2 hρ.1.w) (sq2 hψ.1.w)
    (isPullback_squareMapOfCompatibleMorphism hρ.1.w hρ.1) (isPullback_squareMapOfCompatibleMorphism hψ.1.w hψ.1)
    (grpSchemeSquareProductMap_comp hρ.1.w hψ.1.w ha.w hg.w hc) (μ[G].left ≫ g) (μ[A].left ≫ a)
    (by rw [Category.assoc, hg.w, ← Category.assoc, Over.w]) (by
      rw [← Category.assoc, mul_sq hρ _ (grpSchemeSquareProductMap_comp_fst _) (grpSchemeSquareProductMap_comp_snd _), Category.assoc, ← hc, ← Category.assoc,
        ← mul_sq hψ _ (grpSchemeSquareProductMap_comp_fst _) (grpSchemeSquareProductMap_comp_snd _), Category.assoc])

  obtain ⟨hi, hi1, hi2, hi3⟩ := GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base (spMap (algebraMap R W)) (spMap (algebraMap R K)) (spMap (algebraMap K K')) (spMap (algebraMap W K')) hsq X.hom X.hom G.hom g hg A.hom a ha
    ((Over.pullback (spMap (algebraMap W K'))).obj G).hom (pullback.fst G.hom (spMap (algebraMap W K'))) (eI.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) hρ.1 hψ.1 hc
    (ι[G].left ≫ g) (ι[A].left ≫ a) (by rw [Category.assoc, hg.w, ← Category.assoc, Over.w]) (by
      rw [← Category.assoc, inv_sq hρ, Category.assoc, ← hc, ← Category.assoc, ← inv_sq hψ, Category.assoc])

  obtain ⟨hu, hu1, hu2, hu3⟩ := GlobalTheory.T.exists_desc_of_flat_of_schemeTheoreticallyDominant_base (spMap (algebraMap R W)) (spMap (algebraMap R K)) (spMap (algebraMap K K')) (spMap (algebraMap W K')) hsq X.hom (𝟙 (Sp R)) (𝟙 (Sp W)) (spMap (algebraMap R W))
    (IsPullback.of_vert_isIso ⟨by simp⟩) (𝟙 (Sp K)) (spMap (algebraMap R K)) (IsPullback.of_vert_isIso ⟨by simp⟩)
    (𝟙 (Sp K')) (spMap (algebraMap W K')) (spMap (algebraMap K K')) (IsPullback.of_vert_isIso ⟨by simp⟩) (IsPullback.of_vert_isIso ⟨by simp⟩) hsq.w.symm
    (η[G].left ≫ g) (η[A].left ≫ a) (by rw [Category.assoc, hg.w, ← Category.assoc, Over.w]; rfl) (by
      rw [← Category.assoc, one_sq hρ, Category.assoc, ← hc, ← Category.assoc, ← one_sq hψ, Category.assoc])

  let m : X ⊗ X ⟶ X := Over.homMk hm hm3
  let i : X ⟶ X := Over.homMk hi hi3
  let e₀ : 𝟙_ (Over (Sp R)) ⟶ X := Over.homMk hu hu3
  obtain ⟨_, hμ, -, -, hcX, -⟩ := GrpFlatDesc.grpObj_of_flat_cover (spMap (algebraMap R W)) X G g hg m i e₀
    (fun φ₂ h₂ => by rw [grpSchemeSquareProductMap_eq_tensorHom hg.w h₂]; exact hm1) hi1 hu1
  have hXab : IsAbelianScheme X := ⟨hcX, hXs, hXp, hXc⟩
  have hAX : IsGrpPullback A X (spMap (algebraMap R K)) a := by
    refine ⟨ha, fun T x y x₀ y₀ hx hy => ?_⟩
    obtain rfl : x₀ = pushPt ha.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = pushPt ha.w y := Over.OverMorphism.ext hy
    have := GrpDense.pushPt_mul ha.w (m := μ[X]) (fun φ₂ h₂ => by rw [grpSchemeSquareProductMap_eq_tensorHom ha.w h₂, hμ]; exact hm2) x y
    rw [Hom.mul_def, this]
    rfl
  obtain ⟨e', he', -⟩ := grpPullback_iso (isGrpPullback_pullback X (spMap (algebraMap R K))) hAX
  exact ⟨X, inferInstance, hXab, e', he'⟩

end GlobalTheory.GoodDescW

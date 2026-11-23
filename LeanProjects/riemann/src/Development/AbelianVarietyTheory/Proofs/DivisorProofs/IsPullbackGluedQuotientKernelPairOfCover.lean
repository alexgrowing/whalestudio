import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GlueQuotPB

theorem isIso_of_isPullback_openCover {X Y : Scheme.{0}} (f : X ⟶ Y) (𝒱 : Y.OpenCover)
    {Z : 𝒱.I₀ → Scheme.{0}} (k : ∀ i, Z i ⟶ X) (g : ∀ i, Z i ⟶ 𝒱.X i)
    (h : ∀ i, IsPullback (k i) (g i) f (𝒱.f i)) (hg : ∀ i, IsIso (g i)) : IsIso f := by
  have key := (IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme.{0})
    (f := f) 𝒱).2
  refine key fun i => ?_
  have e : ((h i).isoIsPullback _ _ (IsPullback.of_hasPullback f (𝒱.f i))).hom ≫
      pullback.snd f (𝒱.f i) = g i := by simp
  change IsIso (pullback.snd f (𝒱.f i))
  have hgi := hg i
  have e2 : pullback.snd f (𝒱.f i) =
      ((h i).isoIsPullback _ _ (IsPullback.of_hasPullback f (𝒱.f i))).inv ≫ g i := by
    exact (Iso.eq_inv_comp _).2 e
  rw [e2]
  infer_instance

theorem isIso_of_pullback_openCover {S : Scheme.{0}} (𝒰 : S.OpenCover) {X Y : Over S} (c : X ⟶ Y)
    (hc : ∀ j, IsIso ((Over.pullback (𝒰.f j)).map c)) : IsIso c := by
  suffices hl : IsIso c.left by
    have : IsIso ((Over.forget S).map c) := hl
    exact isIso_of_reflects_iso c (Over.forget S)
  refine isIso_of_isPullback_openCover c.left (𝒰.pullback₁ Y.hom)
    (fun j => pullback.fst X.hom (𝒰.f j)) (fun j => ((Over.pullback (𝒰.f j)).map c).left) (fun j => ?_)
    (fun j => by
      have := hc j
      exact (inferInstance : IsIso ((Over.forget _).map ((Over.pullback (𝒰.f j)).map c))))
  refine IsPullback.of_bot (v₂₁ := pullback.snd Y.hom (𝒰.f j)) (v₂₂ := Y.hom) (h₃₁ := 𝒰.f j) ?_ ?_
    (IsPullback.of_hasPullback Y.hom (𝒰.f j))
  · convert IsPullback.of_hasPullback X.hom (𝒰.f j) using 1
    · simp only [Over.pullback_map_left]
      erw [pullback.lift_snd]
    · exact Over.w c
  · change _ = _ ≫ pullback.fst Y.hom (𝒰.f j)
    simp only [Over.pullback_map_left]
    erw [pullback.lift_fst]

theorem hom_ext_of_pullback_openCover {S : Scheme.{0}} (𝒰 : S.OpenCover) {X Y : Over S} (f g : X ⟶ Y)
    (h : ∀ j, (Over.pullback (𝒰.f j)).map f = (Over.pullback (𝒰.f j)).map g) : f = g := by
  ext1
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ X.hom) _ _ fun j => ?_
  have e := congrArg (fun u => u.left ≫ pullback.fst Y.hom (𝒰.f j)) (h j)
  change pullback.fst X.hom (𝒰.f j) ≫ f.left = pullback.fst X.hom (𝒰.f j) ≫ g.left
  simp only [Over.pullback_map_left] at e
  erw [pullback.lift_fst, pullback.lift_fst] at e
  exact e

theorem baseChange_translation {T T' : Scheme.{0}} (t : T' ⟶ T) (A H : Over T) [GrpObj A] [GrpObj H] (i : H ⟶ A) :
    ∃ e : (Over.pullback t).obj (H ⊗ A) ≅ (Over.pullback t).obj H ⊗ (Over.pullback t).obj A,
      e.hom ≫ ((fst ((Over.pullback t).obj H) ((Over.pullback t).obj A) ≫ (Over.pullback t).map i) *
          snd ((Over.pullback t).obj H) ((Over.pullback t).obj A)) =
        (Over.pullback t).map ((fst H A ≫ i) * snd H A) ∧
      e.hom ≫ snd ((Over.pullback t).obj H) ((Over.pullback t).obj A) = (Over.pullback t).map (snd H A) := by
  refine ⟨(Functor.Monoidal.μIso (Over.pullback t) H A).symm, ?_, ?_⟩
  · rw [Iso.symm_hom, Functor.Monoidal.μIso_inv, MonObj.comp_mul, Functor.map_mul, Functor.map_comp,
      Functor.OplaxMonoidal.δ_fst_assoc, Functor.OplaxMonoidal.δ_snd]
  · rw [Iso.symm_hom, Functor.Monoidal.μIso_inv, Functor.OplaxMonoidal.δ_snd]

theorem isPullback_translation_of_cover : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H G : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) → (∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) Q Q := by
  intro S 𝒰 A H G _ _ i Q B ψ q hψ hq hloc

  let φ : ∀ j, B j ≅ (Over.pullback (𝒰.f j)).obj G := fun j =>
    Over.isoMk (hψ j).isoPullback (by simp)
  have hQ : ∀ j, (Over.pullback (𝒰.f j)).map Q = q j ≫ (φ j).hom := by
    intro j
    ext1
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, Over.comp_left, Category.assoc]
      erw [pullback.lift_fst]
      simp [φ, hq j]
    · simp only [Over.pullback_map_left, Over.comp_left, Category.assoc]
      erw [pullback.lift_snd]
      simp [φ]
  choose e he₁ he₂ using fun j => baseChange_translation (𝒰.f j) A H i
  have w : ((fst H A ≫ i) * snd H A) ≫ Q = snd H A ≫ Q := by
    refine hom_ext_of_pullback_openCover 𝒰 _ _ fun j => ?_
    rw [Functor.map_comp, Functor.map_comp, ← he₁ j, ← he₂ j, hQ j, Category.assoc, Category.assoc,
      (hloc j).w_assoc]
  have hF : ∀ j, IsPullback ((Over.pullback (𝒰.f j)).map ((fst H A ≫ i) * snd H A))
      ((Over.pullback (𝒰.f j)).map (snd H A)) ((Over.pullback (𝒰.f j)).map Q)
      ((Over.pullback (𝒰.f j)).map Q) := by
    intro j
    refine IsPullback.of_iso (hloc j) (e j).symm (Iso.refl _) (Iso.refl _) (φ j) ?_ ?_ ?_ ?_
    · simp [← he₁ j]
    · simp [← he₂ j]
    · simp [hQ j]
    · simp [hQ j]
  let c : H ⊗ A ⟶ pullback Q Q := pullback.lift _ _ w
  have hc : IsIso c := by
    refine isIso_of_pullback_openCover 𝒰 c fun j => ?_
    have hP := (IsPullback.of_hasPullback Q Q).map (Over.pullback (𝒰.f j))
    have : (Over.pullback (𝒰.f j)).map c = ((hF j).isoIsPullback _ _ hP).hom := by
      apply hP.hom_ext
      · rw [IsPullback.isoIsPullback_hom_fst, ← Functor.map_comp]
        exact congrArg (Over.pullback (𝒰.f j)).map (pullback.lift_fst _ _ w)
      · rw [IsPullback.isoIsPullback_hom_snd, ← Functor.map_comp]
        exact congrArg (Over.pullback (𝒰.f j)).map (pullback.lift_snd _ _ w)
    rw [this]
    infer_instance
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso c) (pullback.lift_fst _ _ w)
    (pullback.lift_snd _ _ w)

end GlobalTheory.GlueQuotPB

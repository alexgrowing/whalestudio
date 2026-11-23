import Development.EtaleCohomology.EtaleTrace.GenOutPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def GenOnAgree : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (U U' : X.Opens) (πU : U.toScheme ⟶ PN k N) (πU' : U'.toScheme ⟶ PN k N),
  GenOn p w U πU → GenOn p w U' πU' → pullback.fst U.ι U'.ι ≫ πU = pullback.snd U.ι U'.ι ≫ πU'

def GenOnGen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (π : X ⟶ PN k N) (U : X.Opens),
  genericPoint X ∈ U → GenOn p w U (U.ι ≫ π) → Gen p π w

theorem GenOutGlue_of (h1 : GenOnAgree) (h2 : GenOnGen) : GenOutGlue := by
  intro k _ X _ p N w hloc
  choose U πU hxU hover hgen using hloc
  have hcov : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨x, hxU x⟩
  let 𝒰 := X.openCoverOfIsOpenCover U hcov
  have hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ πU x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ πU y :=
    fun x y => h1 k p N w (U x) (U y) (πU x) (πU y) (hgen x) (hgen y)
  refine ⟨𝒰.glueMorphisms πU hf, ?_, ?_⟩
  · refine 𝒰.hom_ext _ _ fun x => ?_
    have e : 𝒰.f x ≫ 𝒰.glueMorphisms πU hf = πU x := 𝒰.ι_glueMorphisms πU hf x
    rw [← Category.assoc, e]
    exact hover x
  · have hη := 𝒰.ι_glueMorphisms πU hf (genericPoint X)
    refine h2 k p N w _ (U (genericPoint X)) (hxU _) ?_
    have : (U (genericPoint X)).ι ≫ 𝒰.glueMorphisms πU hf = πU (genericPoint X) := hη
    rw [this]
    exact hgen _

theorem genOnGen : GenOnGen := by
  intro k _ X _ p N w π U hη hG n hn f hf
  obtain ⟨h1, h2⟩ := hG hη n hn f hf
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact Iff.rfl
  · intro m g hg h
    have h' := h2 m g hg h
    have hinj : Function.Injective (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom :=
      haveI : IsIso (U.ι.stalkMap ⟨genericPoint X, hη⟩) :=
        (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
      ((asIso (U.ι.stalkMap ⟨genericPoint X, hη⟩)).commRingCatIsoToRingEquiv).injective
    apply hinj
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) ?_ (map_pow _ _ _)).trans h')
    rw [Scheme.Hom.comp_app]
    exact (Scheme.Hom.germ_stalkMap_apply U.ι (π ⁻¹ᵁ Proj.basicOpen _ f) ⟨genericPoint X, hη⟩ h
      (π.app _ (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))))

theorem GenOutGlue_of_agree (h1 : GenOnAgree) : GenOutGlue :=
  GenOutGlue_of h1 genOnGen

end LateralTheory.EtaleTrace.Cov

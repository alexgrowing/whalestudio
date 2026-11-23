import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.Model

variable {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω]

theorem galMap_geomMap {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
    (u : X ⟶ Y) (hu : u ≫ q = p) (σ : Ω ≃ₐ[k] Ω) :
    galMap Ω p σ ≫ geomMap Ω p u hu = geomMap Ω p u hu ≫ galMap Ω q σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, galMap_fst, geomMap, pullback.lift_fst, ← Category.assoc, galMap_fst]
  · rw [Category.assoc, Category.assoc, galMap_snd, geomMap, pullback.lift_snd, pullback.lift_snd_assoc, galMap_snd]

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem gal_pull {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
    (u : X ⟶ Y) (hu : u ≫ q = p) (σ : Ω ≃ₐ[k] Ω) (n : ℕ) (x : H R n (geom Ω q)) :
    gal R Ω p n σ (pull R n (geomMap Ω p u hu) x) = pull R n (geomMap Ω p u hu) (gal R Ω q n σ x) := by
  change pull R n (galMap Ω p σ) (pull R n (geomMap Ω p u hu) x) =
    pull R n (geomMap Ω p u hu) (pull R n (galMap Ω q σ) x)
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← pull_comp, ← pull_comp, galMap_geomMap]

theorem coefPre_isSheaf : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (coefPre R) := by
  haveI : ReflectsLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} R))) :=
    reflectsLimitsOfSize_shrink.{1, 0, 0, 1} _
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget (ModuleCat.{1} (ULift.{1} R)))
  have h := (isSheaf_fpqcTopology_continuousMapPresheaf.{0} R).of_le Scheme.proetaleTopology_le_fpqcTopology
  have e : coefPre R ⋙ forget (ModuleCat.{1} (ULift.{1} R)) = continuousMapPresheaf.{0} R ⋙ uliftFunctor.{1} := rfl
  rw [e]
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ _ h

def coefIso : coef R ≅ (⟨coefPre R, coefPre_isSheaf R⟩ : Shv R) :=
  (asIso (sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).counit).app
    ⟨coefPre R, coefPre_isSheaf R⟩

def homEquiv (X : Scheme.{0}) : ((freeOn R).obj X ⟶ coef R) ≃ C(X, R) := by
  refine (Iso.homCongr (Iso.refl _) (coefIso R)).trans ?_
  refine ((sheafificationAdjunction _ _).homEquiv _ _).trans ?_
  refine (((ModuleCat.adj (ULift.{1} R)).whiskerRight (C := Scheme.{0}ᵒᵖ)).homEquiv _ _).trans ?_
  refine uliftYonedaEquiv.trans ?_
  exact Equiv.ulift

def cohomZeroEquivContinuous (X : Scheme.{0}) : H R 0 X ≃ C(X, R) :=
  Abelian.Ext.homEquiv₀.trans (homEquiv R X)

theorem cohomZero_nontrivial (X : Scheme.{0}) [Nonempty X] [Nontrivial R] : Nontrivial (H R 0 X) :=
  (cohomZeroEquivContinuous R X).nontrivial

example : Nontrivial (H ℤ_[3] 0 (Spec (CommRingCat.of ℚ))) := cohomZero_nontrivial _ _
example : Nontrivial (H (ZMod 5) 0 (Spec (CommRingCat.of ℚ))) := by
  haveI : Fact (1 < 5) := ⟨by norm_num⟩
  exact cohomZero_nontrivial _ _

end GlobalTheory.Et.Model

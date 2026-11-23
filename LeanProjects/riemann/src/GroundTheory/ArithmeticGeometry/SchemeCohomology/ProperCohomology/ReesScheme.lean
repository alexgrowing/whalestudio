import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesSubmodule
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackGamma
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

section Schemes

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Scheme.{u}) [X.Over (Spec (.of A))]

abbrev reesStructure : Spec (.of (reesAlgebra I)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (reesAlgebra I)))

abbrev reesPolyStructure : Spec (.of (Polynomial A)) ⟶ Spec (.of (reesAlgebra I)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (reesAlgebra I) (Polynomial A)))

def reesScheme : Scheme.{u} := pullback (X ↘ Spec (.of A)) (reesStructure I)

def reesPr : reesScheme I X ⟶ X := pullback.fst _ _

def reesSnd : reesScheme I X ⟶ Spec (.of (reesAlgebra I)) := pullback.snd _ _

lemma isPullback_rees :
    IsPullback (reesPr I X) (reesSnd I X) (X ↘ Spec (.of A)) (reesStructure I) :=
  IsPullback.of_hasPullback _ _

instance : (reesScheme I X).Over (Spec (.of (reesAlgebra I))) := ⟨reesSnd I X⟩

instance : IsAffineHom (reesPr I X) :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance

instance [IsProper (X ↘ Spec (.of A))] :
    IsProper (reesScheme I X ↘ Spec (.of (reesAlgebra I))) := by
  change IsProper (pullback.snd (X ↘ Spec (.of A)) (reesStructure I))
  infer_instance

def reesPolyScheme : Scheme.{u} := pullback (reesSnd I X) (reesPolyStructure I)

def reesPolyMap : reesPolyScheme I X ⟶ reesScheme I X := pullback.fst _ _

def reesPolySnd : reesPolyScheme I X ⟶ Spec (.of (Polynomial A)) := pullback.snd _ _

lemma isPullback_reesPoly :
    IsPullback (reesPolyMap I X) (reesPolySnd I X) (reesSnd I X) (reesPolyStructure I) :=
  IsPullback.of_hasPullback _ _

instance : IsAffineHom (reesPolyMap I X) :=
  isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance

end Schemes

section Rings

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]

variable (X) in

def algV (V : X.Opens) : A →+* Γ(X, V) :=
  ((X ↘ Spec (.of A)).appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom

variable {V : X.Opens} (hV : IsAffineOpen V)

variable (I) in

def reesInr (V : X.Opens) : CommRingCat.of (reesAlgebra I) ⟶ Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) :=
  (Scheme.ΓSpecIso (.of (reesAlgebra I))).inv ≫ (reesSnd I X).appLE ⊤ _ le_top

variable (I) in

def polyInr (V : X.Opens) : CommRingCat.of (Polynomial A) ⟶
    Γ(reesPolyScheme I X, reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) :=
  (Scheme.ΓSpecIso (.of (Polynomial A))).inv ≫ (reesPolySnd I X).appLE ⊤ _ le_top

include hV in

theorem isPushout_rees :
    IsPushout (CommRingCat.ofHom (algV X V)) (CommRingCat.ofHom (algebraMap A (reesAlgebra I)))
      ((reesPr I X).app V) (reesInr I V) := by
  refine (isPushout_app_of_isPullback (isPullback_rees I X) hV).of_iso
    (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Scheme.ΓSpecIso (.of (reesAlgebra I))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simp [algV]
  · exact Scheme.ΓSpecIso_naturality _
  · simp
  · simp [reesInr]

include hV in

theorem isPushout_reesPoly :
    IsPushout (CommRingCat.ofHom (algV X V)) (CommRingCat.ofHom (Polynomial.C))
      ((reesPr I X).app V ≫ (reesPolyMap I X).app _) (polyInr I V) := by
  have h1 := (isPushout_app_of_isPullback (isPullback_rees I X) hV).flip
  have h2 := (isPushout_app_of_isPullback (isPullback_reesPoly I X) (hV.preimage (reesPr I X))).flip
  have h := (h1.paste_horiz h2).flip
  refine h.of_iso (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Scheme.ΓSpecIso (.of (Polynomial A)))
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [algV]
  · rw [Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, Scheme.ΓSpecIso_naturality,
      Category.assoc]
    rfl
  · simp
  · simp [polyInr]

end Rings

end

end GroundTheory.Arith.SchemeCoh

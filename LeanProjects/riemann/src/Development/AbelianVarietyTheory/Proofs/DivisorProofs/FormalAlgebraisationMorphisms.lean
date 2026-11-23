import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckExistenceClosedSubschemesSeparatedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismEqOfEqOnThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfProperIsIsoOnReductionsStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlgMorphisms

variable {R : Type} [CommRing R]

instance isClosedImmersion_thick (I : Ideal R) (e : ℕ) : IsClosedImmersion (thick R I e) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem isPullback_trans {I : Ideal R} (X : Over (Spec (CommRingCat.of R)))
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left)
    (hb : ∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) (hβ : ∀ e, β e ≫ b (e + 1) = b e)
    (e : ℕ) : IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e) := by
  have hw : β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ thickTrans R I e := by
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, ← (hb (e + 1)).w, ← Category.assoc,
      hβ, (hb e).w, Category.assoc, thickTrans_comp]
  refine IsPullback.of_right ?_ hw (hb (e + 1))
  rw [hβ, thickTrans_comp]
  exact hb e

theorem formalAlgebraisation_morphisms : GlobalTheory.Published.FormalAlgebraisation.Morphisms := by
  intro R _ _ I hI X Z hX hZs hZl hZq Y β b hb hβ f hf hfβ
  have hIj : I ≤ Ideal.jacobson ⊥ := by
    haveI := hI
    exact IsAdicComplete.le_jacobson_bot I

  let fW : pullback X.hom Z.hom ⟶ Spec (CommRingCat.of R) := pullback.fst X.hom Z.hom ≫ X.hom
  haveI : IsSeparated (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (IsPullback.of_hasPullback X.hom Z.hom).flip hZs
  haveI : LocallyOfFiniteType (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback X.hom Z.hom).flip hZl
  haveI : QuasiCompact (pullback.fst X.hom Z.hom) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback X.hom Z.hom).flip hZq
  have hAlg : Alg fW I := GlobalTheory.T.grothendieck_existence_closedSubschemes_separated R I hI _ fW inferInstance inferInstance inferInstance

  have hcomm : ∀ e, b e ≫ X.hom = f e ≫ Z.hom := fun e => by rw [(hb e).w, hf e]
  let j : ∀ e, (Y e).left ⟶ pullback X.hom Z.hom := fun e => pullback.lift (b e) (f e) (hcomm e)
  have hj₁ : ∀ e, j e ≫ pullback.fst X.hom Z.hom = b e := fun e => pullback.lift_fst _ _ _
  have hj₂ : ∀ e, j e ≫ pullback.snd X.hom Z.hom = f e := fun e => pullback.lift_snd _ _ _
  have hbci : ∀ e, IsClosedImmersion (b e) := fun e =>
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hb e).flip inferInstance
  have hjci : ∀ e, IsClosedImmersion (j e) := fun e => by
    haveI : IsClosedImmersion (j e ≫ pullback.fst X.hom Z.hom) := by rw [hj₁]; exact hbci e
    exact IsClosedImmersion.of_comp (j e) (pullback.fst X.hom Z.hom)
  have hjf : ∀ e, j e ≫ fW = (Y e).hom ≫ thick R I e := fun e => by
    simp only [fW]
    rw [← Category.assoc, hj₁, (hb e).w]
  have hjβ : ∀ e, β e ≫ j (e + 1) = j e := fun e => by
    apply pullback.hom_ext
    · rw [Category.assoc, hj₁, hj₁, hβ]
    · rw [Category.assoc, hj₂, hj₂, hfβ]
  have hYp : ∀ e, IsProper (Y e).hom := fun e =>
    MorphismProperty.of_isPullback (P := @IsProper) (hb e) hX
  obtain ⟨T, i, c, hi, hip, hci, hcpb⟩ := GlobalTheory.T.formal_algebraisation_tower R I _ fW hAlg Y β
    (isPullback_trans X Y β b hb hβ) hYp j hjci hjf hjβ

  let φ : T ⟶ X.left := i ≫ pullback.fst X.hom Z.hom
  have hφX : φ ≫ X.hom = i ≫ fW := Category.assoc _ _ _
  haveI : IsProper (φ ≫ X.hom) := by rw [hφX]; exact hip
  haveI : IsProper φ := IsProper.of_comp φ X.hom
  have hcφ : ∀ e, c e ≫ φ = b e := fun e => by
    simp only [φ]
    rw [← Category.assoc, hci, hj₁]
  haveI hφiso : IsIso φ := GlobalTheory.T.isIso_of_proper_isIso_on_reductions R I hIj T X.left φ X.hom inferInstance hX Y c
    (fun e => by rw [hφX]; exact hcpb e) (fun e => by rw [hcφ]; exact hb e)

  let gl : X.left ⟶ Z.left := inv φ ≫ i ≫ pullback.snd X.hom Z.hom
  have hgw : gl ≫ Z.hom = X.hom := by
    simp only [gl, Category.assoc]
    rw [← pullback.condition, ← Category.assoc i, ← Category.assoc (inv φ)]
    exact IsIso.inv_hom_id_assoc φ X.hom
  refine ⟨Over.homMk gl hgw, fun e => ?_, fun g' hg' => ?_⟩
  · show b e ≫ gl = f e
    simp only [gl]
    rw [← hcφ e, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, hci, hj₂]
  · refine GlobalTheory.T.morphism_eq_of_eq_on_thickenings R I hIj X Z hX hZs Y b hb g' _ fun e => ?_
    rw [hg' e]
    show f e = b e ≫ gl
    simp only [gl]
    rw [← hcφ e, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc, hci, hj₂]

end GlobalTheory.FormalAlgMorphisms

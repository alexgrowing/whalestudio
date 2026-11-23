import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

noncomputable section

private def swapF {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.snd p U.hom ≫ U.hom) ι ⟶ pullback (pullback.fst p ι ≫ p) U.hom :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition, pullback.condition]))
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition])

private def swapB {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.fst p ι ≫ p) U.hom ⟶ pullback (pullback.snd p U.hom ≫ U.hom) ι :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition))
    (pullback.fst _ _ ≫ pullback.snd _ _)
    (by
      rw [pullback.lift_snd_assoc, ← pullback.condition, Category.assoc, pullback.condition])

private def swapI {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (U : B.Etale) :
    pullback (pullback.snd p U.hom ≫ U.hom) ι ≅ pullback (pullback.fst p ι ≫ p) U.hom where
  hom := swapF p ι U
  inv := swapB p ι U
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [swapF, swapB, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

private def baseI {B : Scheme.{0}} (U : B.Etale) : U.left ≅ pullback (𝟙 B) U.hom where
  hom := pullback.lift U.hom (𝟙 _) (by simp)
  inv := pullback.snd _ _
  hom_inv_id := by simp [pullback.lift_snd]
  inv_hom_id := by
    apply pullback.hom_ext
    · have h := pullback.condition (f := 𝟙 B) (g := U.hom)
      simp only [Category.comp_id] at h
      rw [Category.assoc, pullback.lift_fst, Category.id_comp, h]
    · simp [pullback.lift_snd]

theorem UpperTheory.nonempty_iso_relativeEtaleFamily_baseChange :
    ∀ {B Y W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B), Nonempty (gYW p ι ≅ gY (pullback.fst p ι ≫ p)) ∧ Nonempty (gB B ≅ gY (𝟙 B)) ∧ Nonempty (gBW ι ≅ gY ι) := by
  intro B Y W p ι
  refine ⟨⟨NatIso.ofComponents (fun U => swapI p ι U) ?_⟩,
    ⟨NatIso.ofComponents (fun U => baseI U) ?_⟩,
    ⟨NatIso.ofComponents (fun U => pullbackSymmetry U.hom ι) ?_⟩⟩
  · intro U U' a
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [swapI, swapF, gYW, gY, resY, resYW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [swapI, swapF, gYW, gY, resY, resYW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · intro U U' a
    have hw : a.left ≫ U'.hom = U.hom := by simpa using a.w
    apply pullback.hom_ext <;> simp [baseI, gB, gY, resY, pullback.map, hw, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · intro U U' a
    apply pullback.hom_ext <;>
      simp [gBW, gY, resY, resBW, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

end

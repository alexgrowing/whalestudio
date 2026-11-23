import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegRel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvOfFamAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingPullbackPowerMapLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KernelPointPairing

open GlobalTheory.CechPic

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem lift_mul_lift {T : Over S} (a b a' b' : T ⟶ A) :
    (lift a b : T ⟶ G2 A) * lift a' b' = lift (a * a') (b * b') := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem cube_cls (hA : IsAbelianScheme A) {L : LB (G2 A).left} (hL : L.IsLB) {T : Over S} (a b c : T ⟶ G2 A) :
    pull (a * b * c).left (cls L hL) - pull (a * b).left (cls L hL) - pull (a * c).left (cls L hL)
      - pull (b * c).left (cls L hL) + pull a.left (cls L hL) + pull b.left (cls L hL) + pull c.left (cls L hL)
      - pull (1 : T ⟶ G2 A).left (cls L hL) = 0 := by
  have hA2 : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨t, ht⟩ := GlobalTheory.CubeTop.cubeTheorem S (G2 A) hA2 L hL T a b c
  have e := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [cls_linComb hL, Fin.sum_univ_eight] at e
  simp at e
  rw [← e]
  abel

omit [IsCommMonObj A] in

theorem pull_eq_zero_of_factor {X : Scheme.{0}} {c : Pic X} {Y Z : Scheme.{0}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : pull f c = 0) : pull (g ≫ f) c = 0 := by
  rw [pull_comp, h, map_zero]

variable {P : LB (G2 A).left} (hP : P.IsLB)

theorem lam_eq_zero (hA : IsAbelianScheme A)
    (h₁ : pull (lift (1 : A ⟶ A) (𝟙 A)).left (cls P hP) = 0)
    (h₂ : pull (lift (𝟙 A) (1 : A ⟶ A)).left (cls P hP) = 0) {T : Over S} (x : T ⟶ A)
    (hx : pull (lift (snd A T ≫ x) (fst A T)).left (cls P hP) = 0) :
    lam (cls P hP) (fst T (G2 A) ≫ (lift x 1 : T ⟶ G2 A)) (snd T (G2 A)) = 0 := by
  let W := T ⊗ G2 A
  let x' : W ⟶ A := fst T (G2 A) ≫ x
  let b₁ : W ⟶ A := snd T (G2 A) ≫ fst A A
  let b₂ : W ⟶ A := snd T (G2 A) ≫ snd A A
  have l₁ : ∀ b : W ⟶ A, DiagPairing.pc hP 1 b = 0 := fun b => by
    have e : (lift (1 : W ⟶ A) b) = b ≫ lift (1 : A ⟶ A) (𝟙 A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ h₁
  have l₂ : ∀ a : W ⟶ A, DiagPairing.pc hP a 1 = 0 := fun a => by
    have e : (lift a (1 : W ⟶ A)) = a ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, MonObj.comp_one, Category.comp_id]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ h₂
  have l₃ : DiagPairing.pc hP x' b₂ = 0 := by
    have e : (lift x' b₂) = lift b₂ (fst T (G2 A)) ≫ lift (snd A T ≫ x) (fst A T) := by
      rw [comp_lift, lift_snd_assoc, lift_fst]
    unfold DiagPairing.pc
    rw [e, Over.comp_left]
    exact pull_eq_zero_of_factor _ _ hx
  have one : (1 : W ⟶ G2 A) = lift 1 1 := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have ea : fst T (G2 A) ≫ (lift x 1 : T ⟶ G2 A) = lift x' 1 := by
    rw [comp_lift, MonObj.comp_one]
  have eb : snd T (G2 A) = lift b₁ b₂ := by
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have e := cube_cls hA hP (lift x' 1) (lift b₁ 1) (lift 1 b₂)
  simp only [lift_mul_lift, _root_.mul_one, _root_.one_mul, one] at e
  change DiagPairing.pc hP (x' * b₁) b₂ - DiagPairing.pc hP (x' * b₁) 1 - DiagPairing.pc hP x' b₂
    - DiagPairing.pc hP b₁ b₂ + DiagPairing.pc hP x' 1 + DiagPairing.pc hP b₁ 1 + DiagPairing.pc hP 1 b₂
    - DiagPairing.pc hP 1 1 = 0 at e
  rw [l₁, l₁, l₂, l₂, l₂, l₃] at e
  rw [lam, ea, eb, one, lift_mul_lift, _root_.one_mul]
  change DiagPairing.pc hP (x' * b₁) b₂ - DiagPairing.pc hP x' 1 - DiagPairing.pc hP b₁ b₂ + DiagPairing.pc hP 1 1 = 0
  rw [l₁, l₂, ← e]
  abel

end GlobalTheory.KernelPointPairing

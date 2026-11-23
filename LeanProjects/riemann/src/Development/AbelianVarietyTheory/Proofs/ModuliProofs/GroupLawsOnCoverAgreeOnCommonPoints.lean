import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverOpCompat

section
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

private lemma isGrpPullback_one_left (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} (ρ : T ⟶ S') :
    (1 : Over.mk (ρ ≫ f) ⟶ G).left = (1 : Over.mk ρ ⟶ G').left ≫ φ := by

  have hw : ((1 : Over.mk ρ ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (ρ ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let u : Over.mk (ρ ≫ f) ⟶ G := Over.homMk _ hw
  have huu : (u * u).left = ((1 : Over.mk ρ ⟶ G') * 1).left ≫ φ := h.2 (Over.mk ρ) 1 1 u u rfl rfl
  rw [_root_.mul_one] at huu
  have hsq : u * u = u := Over.OverMorphism.ext huu
  have hu : u = 1 := by
    calc u = u * u * u⁻¹ := (_root_.mul_inv_cancel_right u u).symm
      _ = 1 := by rw [hsq, _root_.mul_inv_cancel]
  rw [← hu]
  rfl

theorem push_mul (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p q : Over.mk ρ ⟶ G') (x y : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) (hy : y.left = q.left ≫ φ) :
    (x * y).left = (p * q).left ≫ φ := by
  subst e
  exact h.2 (Over.mk ρ) p q x y hx hy

theorem push_inv (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p : Over.mk ρ ⟶ G') (x : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) :
    (x⁻¹).left = (p⁻¹).left ≫ φ := by
  subst e

  have hw : ((p⁻¹).left ≫ φ) ≫ G.hom = (Over.mk (ρ ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let z : Over.mk (ρ ≫ f) ⟶ G := Over.homMk _ hw
  have hxz : (x * z).left = (p * p⁻¹).left ≫ φ := push_mul h rfl p p⁻¹ x z hx rfl
  rw [_root_.mul_inv_cancel, ← isGrpPullback_one_left h ρ] at hxz
  have hxz' : x * z = 1 := Over.OverMorphism.ext hxz
  have hz : x⁻¹ = z := (_root_.eq_inv_of_mul_eq_one_right hxz').symm
  rw [hz]
  rfl

theorem push_one (h : IsGrpPullback G' G f φ) :
    f ≫ (1 : Out.baseOver S ⟶ G).left = (1 : Out.baseOver S' ⟶ G').left ≫ φ := by

  let c : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
    Over.homMk f (by simp [Out.baseOver])
  have hc : c ≫ (1 : Out.baseOver S ⟶ G) = 1 := MonObj.comp_one c
  have hl : f ≫ (1 : Out.baseOver S ⟶ G).left = (1 : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ G).left := by
    rw [← hc]
    rfl
  rw [hl]
  exact isGrpPullback_one_left h (Out.baseOver S').hom

end

theorem opCompat : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (B : ∀ i j, Over (U i ⊓ U j).toScheme) [∀ i j, GrpObj (B i j)] (a : ∀ i j, (B i j).left ⟶ (G i).left) (b : ∀ i j, (B i j).left ⟶ (G j).left), (∀ i, IsPullback (ψ i) (G i).hom A.hom (U i).ι) → (∀ i j, IsGrpPullback (B i j) (G i) (S.homOfLE inf_le_left) (a i j)) → (∀ i j, IsGrpPullback (B i j) (G j) (S.homOfLE inf_le_right) (b i j)) → (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i j (T : Scheme.{0}) (r : T ⟶ (U i).toScheme) (r' : T ⟶ (U j).toScheme) (x y : Over.mk r ⟶ G i) (x' y' : Over.mk r' ⟶ G j), x.left ≫ ψ i = x'.left ≫ ψ j → y.left ≫ ψ i = y'.left ≫ ψ j → (x * y).left ≫ ψ i = (x' * y').left ≫ ψ j ∧ (x⁻¹).left ≫ ψ i = (x'⁻¹).left ≫ ψ j) ∧ ∀ i j, S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ (1 : Out.baseOver (U i).toScheme ⟶ G i).left ≫ ψ i = S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ (1 : Out.baseOver (U j).toScheme ⟶ G j).left ≫ ψ j := by
  intro S I U A G _ ψ B _ a b _ ha hb hsq
  refine ⟨fun i j T r r' x y x' y' hx hy => ?_, fun i j => ?_⟩
  ·
    let p : T ⟶ (B i j).left := (hsq i j).lift x.left x'.left hx
    let q : T ⟶ (B i j).left := (hsq i j).lift y.left y'.left hy
    have hpa : p ≫ a i j = x.left := (hsq i j).lift_fst _ _ _
    have hpb : p ≫ b i j = x'.left := (hsq i j).lift_snd _ _ _
    have hqa : q ≫ a i j = y.left := (hsq i j).lift_fst _ _ _
    have hqb : q ≫ b i j = y'.left := (hsq i j).lift_snd _ _ _
    let ρ : T ⟶ (U i ⊓ U j).toScheme := p ≫ (B i j).hom
    have er : r = ρ ≫ S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) := by
      show r = (p ≫ (B i j).hom) ≫ _
      rw [Category.assoc, ← (ha i j).1.w, ← Category.assoc, hpa]
      exact (Over.w x).symm
    have er' : r' = ρ ≫ S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) := by
      show r' = (p ≫ (B i j).hom) ≫ _
      rw [Category.assoc, ← (hb i j).1.w, ← Category.assoc, hpb]
      exact (Over.w x').symm
    have eq : q ≫ (B i j).hom = ρ := by
      apply (cancel_mono (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).1
      rw [Category.assoc, ← (ha i j).1.w, ← Category.assoc, hqa]
      exact (Over.w y).trans er
    let P : Over.mk ρ ⟶ B i j := Over.homMk p rfl
    let Q : Over.mk ρ ⟶ B i j := Over.homMk q eq
    have m1 := push_mul (ha i j) er P Q x y hpa.symm hqa.symm
    have m2 := push_mul (hb i j) er' P Q x' y' hpb.symm hqb.symm
    have i1 := push_inv (ha i j) er P x hpa.symm
    have i2 := push_inv (hb i j) er' P x' hpb.symm
    refine ⟨?_, ?_⟩
    · rw [m1, m2]
      simp only [Category.assoc]
      rw [(hsq i j).w]
    · rw [i1, i2]
      simp only [Category.assoc]
      rw [(hsq i j).w]
  ·
    have e1 := congrArg (· ≫ ψ i) (push_one (ha i j))
    have e2 := congrArg (· ≫ ψ j) (push_one (hb i j))
    simp only [Category.assoc] at e1 e2
    rw [e1, e2, (hsq i j).w]

end GlobalTheory.CoverOpCompat

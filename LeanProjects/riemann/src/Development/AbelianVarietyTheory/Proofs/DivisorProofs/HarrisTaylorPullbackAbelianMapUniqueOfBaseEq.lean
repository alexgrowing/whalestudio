import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPosOfCoprime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Rigid

open GlobalTheory.CechPic

theorem pull_cls_P {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}
    (m : ObjMap o' o f) : pull m.φ₂ (cls o.P o.isLB) = cls o'.P o'.isLB := by
  rw [← cls_pull o.isLB m.φ₂ (pull_isLB o.isLB m.φ₂)]
  exact ((cls_eq_iff o'.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol).symm

theorem objMap_phi_unique : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (f f' : S' ⟶ S) (m₁ : ObjMap o' o f) (m₂ : ObjMap o' o f'), f = f' → m₁.φ = m₂.φ := by
  intro p _ D R _ b N hN hNp S S' s s' o o' f f' m₁ m₂ hf
  subst hf
  let α : o'.A.left ⟶ o'.A.left := m₂.cart.1.lift m₁.φ o'.A.hom m₁.cart.1.w
  have e₁ : α ≫ m₂.φ = m₁.φ := m₂.cart.1.lift_fst _ _ _
  have e₂ : α ≫ o'.A.hom = o'.A.hom := m₂.cart.1.lift_snd _ _ _
  have hα : IsGrpPullback o'.A o'.A (𝟙 _) α :=
    IsGrpPullback.cancel m₂.cart (by rw [Category.id_comp, e₁]; exact m₁.cart) (by rw [e₂, Category.comp_id])
  let α' : o'.A ⟶ o'.A := Over.homMk α e₂
  let φ₂ : (G2 o'.A).left ⟶ (G2 o'.A).left := (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α')).left
  have sq : IsSquare α φ₂ := by
    constructor
    · show (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α') ≫ fst o'.A o'.A).left = _
      rw [lift_fst]; rfl
    · show (lift (fst o'.A o'.A ≫ α') (snd o'.A o'.A ≫ α') ≫ snd o'.A o'.A).left = _
      rw [lift_snd]; rfl
  have e₃ : φ₂ ≫ m₂.φ₂ = m₁.φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst o.A o.A).left = _ ≫ (fst o.A o.A).left
      rw [Category.assoc, m₂.sq.1, ← Category.assoc, sq.1, Category.assoc, e₁, m₁.sq.1]
    · show (_ ≫ _) ≫ (snd o.A o.A).left = _ ≫ (snd o.A o.A).left
      rw [Category.assoc, m₂.sq.2, ← Category.assoc, sq.2, Category.assoc, e₁, m₁.sq.2]
  have act : ∀ c, (o'.act.act c).left ≫ α = α ≫ (o'.act.act c).left := fun c => by
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, m₂.act, ← Category.assoc, e₁, m₁.act]
    · simp only [Category.assoc, e₂, Over.w]
  have eta : ∀ y, (o'.eta y).left ≫ α = 𝟙 S' ≫ (o'.eta y).left := fun y => by
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, e₁, m₁.eta, Category.id_comp, m₂.eta]
    · rw [Category.assoc, e₂, Category.id_comp]
  have pol : LBIso o'.P (o'.P.pull φ₂) := by
    refine (cls_eq_iff o'.isLB (pull_isLB o'.isLB φ₂)).1 ?_
    rw [cls_pull o'.isLB φ₂]
    conv_lhs => rw [← pull_cls_P m₁]
    rw [← e₃, pull_comp, pull_cls_P m₂]
  let m : ObjMap o' o' (𝟙 S') := ⟨α, φ₂, hα, sq, act, pol, eta⟩
  have h := eq_id p D R b N hN hNp S' s' o' m
  change α = 𝟙 _ at h
  rw [← e₁, h, Category.id_comp]

end GlobalTheory.UPel.HT.Rigid

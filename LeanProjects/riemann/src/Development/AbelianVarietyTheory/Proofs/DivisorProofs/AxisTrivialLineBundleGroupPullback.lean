import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AxisTriv

theorem lift_comp_sq {S T : Scheme.{0}} {A : Over S} {B : Over T} {β : B.left ⟶ A.left}
    {β₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} (hs : IsSquare β β₂) (a b : B ⟶ B) (a' b' : A ⟶ A)
    (ha : a.left ≫ β = β ≫ a'.left) (hb : b.left ≫ β = β ≫ b'.left) :
    (lift a b).left ≫ β₂ = β ≫ (lift a' b').left := by
  have k₁ : (lift a b).left ≫ (fst B B).left = a.left := congrArg (fun z => z.left) (lift_fst a b)
  have k₂ : (lift a' b').left ≫ (fst A A).left = a'.left := congrArg (fun z => z.left) (lift_fst a' b')
  have l₁ : (lift a b).left ≫ (snd B B).left = b.left := congrArg (fun z => z.left) (lift_snd a b)
  have l₂ : (lift a' b').left ≫ (snd A A).left = b'.left := congrArg (fun z => z.left) (lift_snd a' b')
  apply pullback.hom_ext
  · change ((lift a b).left ≫ β₂) ≫ (fst A A).left = (β ≫ (lift a' b').left) ≫ (fst A A).left
    rw [Category.assoc, hs.1, ← Category.assoc, k₁, Category.assoc, k₂, ha]
  · change ((lift a b).left ≫ β₂) ≫ (snd A A).left = (β ≫ (lift a' b').left) ≫ (snd A A).left
    rw [Category.assoc, hs.2, ← Category.assoc, l₁, Category.assoc, l₂, hb]

theorem exists_gen_pull {S T : Scheme.{0}} {A : Over S} {B : Over T} {β : B.left ⟶ A.left}
    {β₂ : (B ⊗ B).left ⟶ (A ⊗ A).left} {P : LB (A ⊗ A).left} (hP : P.IsLB) (a : B ⟶ B ⊗ B) (a' : A ⟶ A ⊗ A)
    (e : a.left ≫ β₂ = β ≫ a'.left) (h : ∃ u : (P.pull a'.left).Gen, u.IsGen) :
    ∃ u : ((P.pull β₂).pull a.left).Gen, u.IsGen := by
  obtain ⟨u, hu⟩ := h
  have i₁ : LBIso ((P.pull β₂).pull a.left) (P.pull (a.left ≫ β₂)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP β₂)) a.left
  have i₂ : LBIso ((P.pull a'.left).pull β) (P.pull (β ≫ a'.left)) :=
    GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP a'.left)) β
  rw [e] at i₁
  have i := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) i₁ i₂.symm
  obtain ⟨w, hw⟩ := i.symm
  obtain ⟨v, hv, -⟩ := GlobalTheory.WtTower.exists_gen_of_iso (pull_isLB (pull_isLB hP _) _) (pull_isLB (pull_isLB hP _) _)
    w hw (pullGenLB u β) (pullGenLB_isGen hu β)
  exact ⟨v, hv⟩

theorem axes_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (G2 A).left), P.IsLB → (∃ u : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, u.IsGen) → (∃ u : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, u.IsGen) → ∀ (t : T ⟶ S) (B : Over T) [GrpObj B] (β : B.left ⟶ A.left) (β₂ : (G2 B).left ⟶ (G2 A).left), IsGrpPullback B A t β → IsSquare β β₂ → (∃ u : ((P.pull β₂).pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen) ∧ (∃ u : ((P.pull β₂).pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen) := by
  intro S T A _ P hP h₁ h₂ t B _ β β₂ h hs
  have e₁ := GlobalTheory.PPAS.one_comp_of_isGrpPullback h
  exact ⟨exists_gen_pull hP _ _ (lift_comp_sq hs _ _ _ _ e₁ rfl) h₁,
    exists_gen_pull hP _ _ (lift_comp_sq hs _ _ _ _ rfl e₁) h₂⟩

end GlobalTheory.AxisTriv

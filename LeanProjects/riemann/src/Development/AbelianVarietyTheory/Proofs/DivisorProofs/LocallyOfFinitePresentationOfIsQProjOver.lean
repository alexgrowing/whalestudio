import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime]

def ObjMap.comp {R : Type} [CommRing R] {D : Datum p} {b : Base D R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}}
    {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) :
    ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
    by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB m₁.φ₂) (pull_isLB o₃.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o₂.P m₁.φ₂ m₁.φ₂ rfl)
      (chartPullSame o₃.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
      m₂.pol)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

end GlobalTheory.UPel.HT

namespace GlobalTheory.RelTan

def TanDim {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (d : ℕ) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (β : R →+* k) (x : Sp k ⟶ X), x ≫ s = spMap β →
    ∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X,
      u ≫ s = spMap ((algebraMap k (TrivSqZeroExt k (Fin d → k))).comp β) ∧
      spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧
      ∀ v : Sp (DualNumber k) ⟶ X, v ≫ s = spMap ((algebraMap k (DualNumber k)).comp β) →
        spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x →
        ∃! φ : TrivSqZeroExt k (Fin d → k) →ₐ[k] DualNumber k, spMap φ.toRingHom ≫ u = v

end GlobalTheory.RelTan

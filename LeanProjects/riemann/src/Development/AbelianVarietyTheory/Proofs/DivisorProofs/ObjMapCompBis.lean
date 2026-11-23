import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

noncomputable section

namespace GlobalTheory.UPel.HT.ObjMapComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {s'' : S'' ⟶ Sp R}
  {o : Obj b N s} {o' : Obj b N s'} {o'' : Obj b N s''} {f : S' ⟶ S} {g : S'' ⟶ S'}

def comp (m₁ : ObjMap o'' o' g) (m₂ : ObjMap o' o f) : ObjMap o'' o (g ≫ f) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
         by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o''.isLB (pull_isLB o'.isLB m₁.φ₂) (pull_isLB o.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o'.P m₁.φ₂ m₁.φ₂ rfl)
      (chartPullSame o.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
      m₂.pol)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

theorem objMap_comp : ∀ {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R]
    {b : GlobalTheory.UPel.HT.Base D R} {N : ℕ} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {s'' : S'' ⟶ Sp R}
    (o : GlobalTheory.UPel.HT.Obj b N s) (o' : GlobalTheory.UPel.HT.Obj b N s') (o'' : GlobalTheory.UPel.HT.Obj b N s'') (f : S' ⟶ S)
    (g : S'' ⟶ S'), GlobalTheory.UPel.HT.ObjMap o'' o' g → GlobalTheory.UPel.HT.ObjMap o' o f →
      Nonempty (GlobalTheory.UPel.HT.ObjMap o'' o (g ≫ f)) :=
  fun _ _ _ _ _ m₁ m₂ => ⟨comp m₁ m₂⟩

end GlobalTheory.UPel.HT.ObjMapComp

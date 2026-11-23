import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj

noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}
  {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp (D.OEp p)} {s₂ : S₂ ⟶ Sp (D.OEp p)} {s₃ : S₃ ⟶ Sp (D.OEp p)}
  {o₁ : Obj D p N s₁} {o₂ : Obj D p N s₂} {o₃ : Obj D p N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}

def ObjMap.comp (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) : ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  act a := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.PP.isLB (pull_isLB o₂.PP.isLB m₁.φ) (pull_isLB o₃.PP.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o₂.PP.L m₁.φ)
      (chartPullSame o₃.PP.L (fun _ : PUnit => m₁.φ ≫ m₂.φ) (fun _ => m₂.φ) (fun _ => 1) m₁.φ (fun _ => rfl))
      m₂.pol)
  eta a := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

theorem objMap_comp : ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (D : GlobalTheory.UPel.Datum F) (p N : ℕ)
    (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp (D.OEp p)) (s₂ : S₂ ⟶ Sp (D.OEp p)) (s₃ : S₃ ⟶ Sp (D.OEp p))
    (o₁ : GlobalTheory.UPel.Obj D p N s₁) (o₂ : GlobalTheory.UPel.Obj D p N s₂) (o₃ : GlobalTheory.UPel.Obj D p N s₃) (f : S₁ ⟶ S₂)
    (g : S₂ ⟶ S₃), GlobalTheory.UPel.ObjMap o₁ o₂ f → GlobalTheory.UPel.ObjMap o₂ o₃ g → Nonempty (GlobalTheory.UPel.ObjMap o₁ o₃ (f ≫ g)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m₁ m₂ => ⟨m₁.comp m₂⟩

end GlobalTheory.UPel

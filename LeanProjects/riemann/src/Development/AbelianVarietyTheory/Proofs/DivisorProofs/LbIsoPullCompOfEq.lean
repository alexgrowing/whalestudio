import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel

theorem lbIso_pull_comp_of_eq {X X₁ X₂ : Scheme.{0}} {M : LB X} {π₁ : X₁ ⟶ X} {π₂ : X₂ ⟶ X} {φ : X₂ ⟶ X₁}
    (hφ : π₂ = φ ≫ π₁) {L₁ : LB X₁} (e : LBIso L₁ (M.pull π₁)) : LBIso (M.pull π₂) (L₁.pull φ) :=
  LBIso.chartPull (chartPullSame M (fun _ : PUnit => π₂) (fun _ => π₁) (fun _ => 1) φ fun _ => hφ)
    (Geo.Tor.chartPullPull L₁ φ φ rfl) e.symm

theorem objMap_cancel : ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (D : GlobalTheory.UPel.Datum F) (p N : ℕ)
    (T X Y : Scheme.{0}) (t : T ⟶ Sp (D.OEp p)) (sX : X ⟶ Sp (D.OEp p)) (sY : Y ⟶ Sp (D.OEp p))
    (o : GlobalTheory.UPel.Obj D p N t) (o₁ : GlobalTheory.UPel.Obj D p N sX) (u : GlobalTheory.UPel.Obj D p N sY) (x : T ⟶ X) (π : X ⟶ Y),
    GlobalTheory.UPel.ObjMap o₁ u π → GlobalTheory.UPel.ObjMap o u (x ≫ π) → Nonempty (GlobalTheory.UPel.ObjMap o o₁ x) := by
  intro F _ _ _ D p N T X Y t sX sY o o₁ u x π m₁ m
  have w : m.φ ≫ u.A.hom = (o.A.hom ≫ x) ≫ π := by rw [m.cart.1.w, Category.assoc]
  let φ := m₁.cart.1.lift m.φ (o.A.hom ≫ x) w
  have hφ : φ ≫ m₁.φ = m.φ := m₁.cart.1.lift_fst _ _ _
  have hφ2 : φ ≫ o₁.A.hom = o.A.hom ≫ x := m₁.cart.1.lift_snd _ _ _
  refine ⟨{ φ := φ, cart := ?_, act := ?_, pol := ?_, eta := ?_ }⟩
  · exact IsGrpPullback.cancel m₁.cart (m.cart.congr rfl hφ.symm) hφ2
  · intro a
    apply m₁.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₁.act, ← Category.assoc, hφ]
    · rw [Category.assoc, Category.assoc, Over.w (o₁.act.act a), hφ2, ← Category.assoc, Over.w (o.act.act a)]
  · exact LBIso.trans o.PP.isLB (pull_isLB u.PP.isLB _) (pull_isLB o₁.PP.isLB φ) m.pol
      (lbIso_pull_comp_of_eq hφ.symm m₁.pol)
  · intro a
    apply m₁.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₁.eta]
    · rw [Category.assoc, hφ2, ← Category.assoc, Over.w (o.eta a), Category.assoc, Over.w (o₁.eta a)]
      simp

end GlobalTheory.UPel

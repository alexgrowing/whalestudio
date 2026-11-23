import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel

noncomputable section

namespace GlobalTheory.UPel.HT.Gen.Unique

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

theorem gObjMap_id {b : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj b N s) :
    Nonempty (GObjMap o o (𝟙 S)) :=
  ⟨{ φ := 𝟙 _
     φ₂ := 𝟙 _
     cart := GlobalTheory.SiegLower.isGrpPullback_id o.A
     sq := ⟨by simp, by simp⟩
     act := fun c => by simp
     pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB
     eta := fun y => by simp }⟩

private theorem lbIso_pull_comp_of_lbIso {X Y Z : Scheme.{0}} {M : LB X} {P : LB Y} {Q : LB Z} {a : X ⟶ Y} {c : Y ⟶ Z}
    (H₁ : LBIso M (P.pull a)) (H₂ : LBIso P (Q.pull c)) (hM : M.IsLB) (hP : P.IsLB) (hQ : Q.IsLB) :
    LBIso M (Q.pull (a ≫ c)) := by
  have E : LBIso (P.pull a) ((Q.pull c).pull a) := SiegelDescent.lbIso_square hP hQ H₂ rfl
  have F : LBIso ((Q.pull c).pull a) ((Q.pull (a ≫ c)).pull (𝟙 X)) :=
    GlobalTheory.FiniteAmple.lbIso_pull_pull c hQ (g := a) (g' := 𝟙 X) (f' := a ≫ c) (by rw [Category.id_comp])
  have hPa := pull_isLB hP a
  have hQc := pull_isLB hQ (a ≫ c)
  exact LBIso.trans hM hPa hQc H₁ (LBIso.trans hPa (pull_isLB (pull_isLB hQ c) a) hQc E
    (LBIso.trans (pull_isLB (pull_isLB hQ c) a) (pull_isLB hQc (𝟙 X)) hQc F (GlobalTheory.SiegLower.lbIso_pull_id hQc).symm))

theorem gObjMap_comp {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) : Nonempty (GObjMap o₁ o₃ (f ≫ g)) :=
  ⟨{ φ := h₁.φ ≫ h₂.φ
     φ₂ := h₁.φ₂ ≫ h₂.φ₂
     cart := IsGrpPullback.comp h₁.cart h₂.cart
     sq := ⟨by rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc],
       by rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]⟩
     act := fun c => by rw [← Category.assoc, h₁.act c, Category.assoc, h₂.act c, ← Category.assoc]
     pol := lbIso_pull_comp_of_lbIso h₁.pol h₂.pol o₁.isLB o₂.isLB o₃.isLB
     eta := fun y => by rw [← Category.assoc, h₁.eta y, Category.assoc, h₂.eta y, ← Category.assoc] }⟩

end GlobalTheory.UPel.HT.Gen.Unique

import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.DiagComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}

theorem diag_comp (m : ObjMap o' o f) :
    (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
  apply pullback.hom_ext
  · have h1 := m.sq.1
    have e1 : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (fst o'.A o'.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have e2 : (lift (𝟙 o.A) (𝟙 o.A)).left ≫ (fst o.A o.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    show _ ≫ (fst o.A o.A).left = _ ≫ (fst o.A o.A).left
    rw [Category.assoc, h1, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]
  · have h2 := m.sq.2
    have e1 : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (snd o'.A o'.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    have e2 : (lift (𝟙 o.A) (𝟙 o.A)).left ≫ (snd o.A o.A).left = 𝟙 _ :=
      congrArg (fun z => z.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    show _ ≫ (snd o.A o.A).left = _ ≫ (snd o.A o.A).left
    rw [Category.assoc, h2, ← Category.assoc, e1, Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem diag_lbIso (m : ObjMap o' o f) :
    LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) := by
  have h₁ : LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (o.P.pull (m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    MapComp.lbIso_pull_comp m.pol _ (diag_comp m).symm
  have h₂ : LBIso ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ)
      (o.P.pull (m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left)) :=
    MapComp.lbIso_pull_comp (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB o.isLB _)) m.φ rfl
  exact LBIso.trans (pull_isLB o'.isLB _) (pull_isLB o.isLB _) (pull_isLB (pull_isLB o.isLB _) _) h₁ h₂.symm

end GlobalTheory.UPel.HT.DiagComp

namespace GlobalTheory.UPel.HT

theorem objMap_comp_diag_lbIso : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S S' S'' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (s'' : S'' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (o'' : Obj b N s'') (f : S' ⟶ S) (f' : S'' ⟶ S'), (Nonempty (ObjMap o'' o' f') → Nonempty (ObjMap o' o f) → Nonempty (ObjMap o'' o (f' ≫ f))) ∧ ∀ m : ObjMap o' o f, LBIso (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull m.φ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    ⟨fun ⟨m₁⟩ ⟨m₂⟩ => ⟨MapComp.comp m₁ m₂⟩, fun m => DiagComp.diag_lbIso m⟩

end GlobalTheory.UPel.HT

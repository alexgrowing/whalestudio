import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

universe w v u

theorem HU_subsingleton_of_obj {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    (F : C ⥤ ModuleCat.{w} R) (U : ObjectProperty C) (j : ℕ)
    (h : ∀ T : C, Subsingleton (F.obj T)) : Subsingleton (HU F U j) := by
  have hC : Subsingleton (CH.Cn (U.ι ⋙ F) j) :=
    ⟨fun f g => funext fun s => (h _).elim _ _⟩
  have hZ : Subsingleton ((CH.cx (U.ι ⋙ F)).Z j) :=
    ⟨fun x y => Subtype.ext (hC.elim _ _)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact congrArg _ (hZ.elim x y)

theorem sq_obj_subsingleton {R : Type} [CommRing R] {C : Type u} [Category.{v} C]
    {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (T : C) (h : a.S T = b.S T) :
    Subsingleton ((sq a b).obj T) := by
  have h0 : ∀ x : sqM a b T, x = 0 := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    refine Subtype.ext ?_
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h ▸ hy)
  exact ⟨fun x y => (h0 x).trans (h0 y).symm⟩

theorem HU_gr_neg {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ) (hr : r < 0) (j : ℕ) :
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := by
  refine HU_subsingleton_of_obj _ Q j fun T => sq_obj_subsingleton _ _ T ?_
  have e : r.toNat = (r + 1).toNat := by omega
  change T.pdPow r.toNat = T.pdPow (r + 1).toNat
  rw [e]

end GlobalTheory.CompanionTheory.Cone

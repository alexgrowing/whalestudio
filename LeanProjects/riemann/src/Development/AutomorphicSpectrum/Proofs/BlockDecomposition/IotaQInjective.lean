import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

section Defs

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

abbrev QC : Type := C1 F ⧸ LinearMap.range (d0 F)

def iotaQ : H1 F →ₗ[R] QC F :=
  Submodule.mapQ _ _ (Z1 F).subtype (by
    rintro _ ⟨g, rfl⟩
    exact ⟨g, rfl⟩)

theorem iotaQ_mk (f : Z1 F) : iotaQ F (H1.mk F f) = Submodule.Quotient.mk f.1 := rfl

theorem iotaQ_injective : Function.Injective (iotaQ F) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [iotaQ_mk, Submodule.Quotient.mk_eq_zero] at hc
  obtain ⟨g, hg⟩ := hc
  exact H1.mk_eq_zero.2 ⟨g, hg⟩

def crossB : H1 F →ₗ[R] H1 F →ₗ[R] H2 (box F) :=
  (cup (box F)).compl₁₂ (boxL F).pull1 (boxR F).pull1

theorem crossB_apply (a b : H1 F) : crossB F a b = cup (box F) ((boxL F).pull1 a) ((boxR F).pull1 b) := rfl

end Defs

section Wedge

variable {R : Type} [CommRing R] (V : Type) [AddCommGroup V] [Module R V]

private theorem upd0 {X : Type} (a b c : X) : Function.update ![a, b] 0 c = ![c, b] := by
  funext i; fin_cases i <;> simp

private theorem upd1 {X : Type} (a b c : X) : Function.update ![a, b] 1 c = ![a, c] := by
  funext i; fin_cases i <;> simp

def wedgeT : V ⊗[R] V →ₗ[R] ⋀[R]^2 V :=
  TensorProduct.lift (LinearMap.mk₂ R (fun a b ↦ exteriorPower.ιMulti R 2 ![a, b])
    (fun a a' b ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_add ![a, b] 0 a a'
      simpa only [upd0, upd1] using this)
    (fun r a b ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_smul ![a, b] 0 r a
      simpa only [upd0, upd1] using this)
    (fun a b b' ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_add ![a, b] 1 b b'
      simpa only [upd0, upd1] using this)
    (fun r a b ↦ by
      have := (exteriorPower.ιMulti R (M := V) 2).map_update_smul ![a, b] 1 r b
      simpa only [upd0, upd1] using this))

theorem wedgeT_tmul (a b : V) : wedgeT (R := R) V (a ⊗ₜ b) = exteriorPower.ιMulti R 2 ![a, b] := rfl

end Wedge

end GlobalTheory.CompanionTheory.WedgeOf

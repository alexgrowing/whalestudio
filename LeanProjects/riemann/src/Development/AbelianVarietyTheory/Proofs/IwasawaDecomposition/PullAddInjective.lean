import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst

noncomputable section

namespace GlobalTheory.PolFan.OrbMark

variable {X Y : Type} [AddCommGroup X] [AddCommGroup Y]

def pullAdd (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) : LinearMap.BilinForm ℤ X :=
  u.compl₁₂ f.toIntLinearMap f.toIntLinearMap

@[simp] theorem pullAdd_apply (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) (x y : X) : pullAdd f u x y = u (f x) (f y) := rfl

theorem pullAdd_injective {f : X →+ Y} (hf : Function.Surjective f) : Function.Injective (pullAdd f) :=
  fun u u' h => LinearMap.ext₂ fun a b => by
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    exact LinearMap.congr_fun₂ h a b

def pullAddLin (f : X →+ Y) : LinearMap.BilinForm ℤ Y →ₗ[ℤ] LinearMap.BilinForm ℤ X where
  toFun := pullAdd f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullAddLin_apply (f : X →+ Y) (u : LinearMap.BilinForm ℤ Y) : pullAddLin f u = pullAdd f u := rfl

example : pullAdd (zmultiplesHom ℤ 2 : ℤ →+ ℤ) mulForm 1 1 = 4 := by simp

end GlobalTheory.PolFan.OrbMark

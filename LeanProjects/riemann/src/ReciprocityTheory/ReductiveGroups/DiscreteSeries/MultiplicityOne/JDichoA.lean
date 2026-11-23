import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

noncomputable section

open MeasureTheory ComplexConjugate
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

def Cj (H : Type*) := H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def toCj (x : H) : Cj H := x

def ofCj (x : Cj H) : H := x

instance : NormedAddCommGroup (Cj H) := inferInstanceAs (NormedAddCommGroup H)

instance instModuleCj : Module ℂ (Cj H) := Module.compHom H (starRingEnd ℂ)

theorem smul_def (c : ℂ) (x : Cj H) : c • x = toCj (conj c • ofCj x) := rfl

instance : NormedSpace ℂ (Cj H) where
  norm_smul_le c x := by
    show ‖(conj c • ofCj x : H)‖ ≤ ‖c‖ * ‖(ofCj x : H)‖
    rw [norm_smul, Complex.norm_conj]

instance : Inner ℂ (Cj H) := ⟨fun x y => ⟪(ofCj y : H), ofCj x⟫_ℂ⟩

theorem inner_def (x y : Cj H) : ⟪x, y⟫_ℂ = ⟪(ofCj y : H), ofCj x⟫_ℂ := rfl

instance : InnerProductSpace ℂ (Cj H) where
  norm_sq_eq_re_inner x := by
    show ‖(ofCj x : H)‖ ^ 2 = RCLike.re ⟪(ofCj x : H), ofCj x⟫_ℂ
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (ofCj x : H)).symm
  conj_inner_symm x y := by
    show conj ⟪(ofCj x : H), ofCj y⟫_ℂ = ⟪(ofCj y : H), ofCj x⟫_ℂ
    exact inner_conj_symm _ _
  add_left x y z := by
    show ⟪(ofCj z : H), ofCj x + ofCj y⟫_ℂ = ⟪(ofCj z : H), ofCj x⟫_ℂ + ⟪(ofCj z : H), ofCj y⟫_ℂ
    exact inner_add_right _ _ _
  smul_left x y r := by
    show ⟪(ofCj y : H), conj r • ofCj x⟫_ℂ = conj r * ⟪(ofCj y : H), ofCj x⟫_ℂ
    exact inner_smul_right _ _ _

instance [CompleteSpace H] : CompleteSpace (Cj H) := inferInstanceAs (CompleteSpace H)

instance [Nontrivial H] : Nontrivial (Cj H) := inferInstanceAs (Nontrivial H)

def opCj (A : H →L[ℂ] H) : Cj H →L[ℂ] Cj H where
  toFun x := toCj (A (ofCj x))
  map_add' x y := A.map_add (ofCj x) (ofCj y)
  map_smul' c x := A.map_smul (conj c) (ofCj x)
  cont := A.continuous

theorem opCj_apply (A : H →L[ℂ] H) (x : Cj H) : opCj A x = toCj (A (ofCj x)) := rfl

def eCj : Cj H ≃ₗᵢ⋆[ℂ] H where
  toFun := ofCj
  invFun := toCj
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' _ := rfl

end ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

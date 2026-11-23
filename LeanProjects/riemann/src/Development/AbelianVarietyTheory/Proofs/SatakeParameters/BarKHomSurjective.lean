import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.IdemAdj

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

variable (E a) in
omit [NumberField E] [IsTotallyComplex E] in

def barKHom : Kinf E a →* Kinf E a where
  toFun := barK
  map_one' := Subtype.ext (by ext i j : 1; simp [barK, Matrix.one_apply])
  map_mul' k k' := Subtype.ext (by
    change Matrix.transpose (star (k.1 * k'.1)) = Matrix.transpose (star k.1) * Matrix.transpose (star k'.1)
    ext i j
    simp [Matrix.mul_apply, Matrix.star_apply, mul_comm])

omit [NumberField E] [IsTotallyComplex E] in
@[simp] theorem barKHom_apply (k : Kinf E a) : barKHom E a k = barK k := rfl

omit [NumberField E] [IsTotallyComplex E] in

theorem barK_barK (k : Kinf E a) : barK (barK k) = k := Subtype.ext (by
  ext i j
  simp [barK, Matrix.star_apply])

omit [NumberField E] [IsTotallyComplex E] in

theorem barKHom_surjective : Function.Surjective (barKHom E a) := fun k => ⟨barK k, barK_barK k⟩

def cptOn (π : CuspSub E a) : Representation ℂ (Kinf E a) π.V where
  toFun k := π.op (.cpt k)
  map_one' := by
    ext φ
    simp [CuspSub.op, act]
  map_mul' k k' := by
    ext φ
    simp [CuspSub.op, act, map_mul]

@[simp] theorem cptOn_apply (π : CuspSub E a) (k : Kinf E a) (φ : π.V) :
    cptOn π k φ = π.op (.cpt k) φ := rfl

@[simp] theorem cptOn_val (π : CuspSub E a) (k : Kinf E a) (φ : π.V) :
    (cptOn π k φ).1 = cptRep E a k φ.1 := rfl

end GlobalTheory.IdemAdj

end

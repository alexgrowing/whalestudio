import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {R : Type} [Zero R] {n : ℕ}

variable (σ) in

def stabAt (X : Spc F E n) (ev : AF F → R) (x : Fin n → E) : Subgroup (UAtSub σ X ev) where
  carrier := {g | mat g.1 *ᵥ incV F x = incV F x}
  one_mem' := by
    show mat (1 : UA σ X.J) *ᵥ incV F x = incV F x
    rw [GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]
  mul_mem' := by
    intro g h hg hh
    show mat (g.1 * h.1) *ᵥ incV F x = incV F x
    rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hh, hg]
  inv_mem' := by
    intro g hg
    show mat g.1⁻¹ *ᵥ incV F x = incV F x
    conv_lhs => rw [← hg]
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one, Matrix.one_mulVec]

theorem mem_stabAt {X : Spc F E n} {ev : AF F → R} {x : Fin n → E} {g : UAtSub σ X ev} :
    g ∈ stabAt σ X ev x ↔ mat g.1 *ᵥ incV F x = incV F x := Iff.rfl

def kIncl {X : Spc F E n} (K : Subgroup (UA σ X.J)) (ev : AF F → R) : KAt K ev →* UAtSub σ X ev :=
  Subgroup.inclusion inf_le_right

@[simp] theorem kIncl_val {X : Spc F E n} (K : Subgroup (UA σ X.J)) (ev : AF F → R) (k : KAt K ev) :
    (kIncl K ev k).1 = k.1 := rfl

variable (E) in

def absPow (ev : AF F → R) (k : ℕ) : idelesAt E ev →* ℝ≥0 :=
  (powMonoidHom k).comp ((absE F E).comp (idelesAt E ev).subtype)

@[simp] theorem absPow_apply (ev : AF F → R) (k : ℕ) (t : idelesAt E ev) : absPow E ev k t = absE F E t.1 ^ k := rfl

end GlobalTheory.ThK.LemF.QuotInv

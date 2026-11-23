import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandE

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

def uval [(subG p K L).Normal] (w : (layerU p K L).V) : PadicAlgCl p :=
  ((Additive.toMul (Subtype.val (p := fun x => x ∈ Ubar p) w.1) : (PadicAlgCl p)ˣ) : PadicAlgCl p)

section

variable [(subG p K L).Normal]

theorem uval_add (a b : (layerU p K L).V) : uval (a + b) = uval a * uval b := rfl

theorem uval_neg (a : (layerU p K L).V) : uval (-a) = (uval a)⁻¹ := Units.val_inv_eq_inv_val _

theorem uval_sub (a b : (layerU p K L).V) : uval (a - b) = uval a * (uval b)⁻¹ := by
  rw [sub_eq_add_neg, uval_add, uval_neg]

theorem uval_sum {ι : Type*} (s : Finset ι) (f : ι → (layerU p K L).V) :
    uval (∑ i ∈ s, f i) = ∏ i ∈ s, uval (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, uval_add, ih]

theorem uval_rho (σ : GK p K) (w : (layerU p K L).V) :
    uval ((layerU p K L).rho (QuotientGroup.mk σ) w) = σ (uval w) := rfl

theorem uval_injective : Injective (uval : (layerU p K L).V → PadicAlgCl p) := fun _ _ hab =>
  Subtype.ext (Subtype.ext (Units.ext hab))

theorem uval_ne_zero (w : (layerU p K L).V) : uval w ≠ 0 := Units.ne_zero _

theorem vbar_eq_zero_iff (x : KbarMult p) :
    vbar p x = 0 ↔ ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpos : 0 < ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ :=
    norm_pos_iff.2 (Units.ne_zero _)
  rw [vbar_apply, neg_eq_zero, Real.logb_eq_zero]
  constructor
  · rintro (h | h | h | h | h | h) <;> linarith
  · intro h; right; right; right; right; left; exact h

theorem norm_uval (w : (layerU p K L).V) : ‖uval w‖ = 1 :=
  (vbar_eq_zero_iff _).1 ((mem_Ubar_iff p _).1 (Subtype.property (p := fun x => x ∈ Ubar p) w.1))

theorem uval_mem (h : K ≤ L) (w : (layerU p K L).V) : uval w ∈ L :=
  (mem_iff_fixed h _).2 fun σ hσ =>
    congrArg (fun y : Ubar p => ((Additive.toMul (y : KbarMult p) : (PadicAlgCl p)ˣ) : PadicAlgCl p))
      (w.2 ⟨σ, hσ⟩)

theorem exists_uval {x : PadicAlgCl p} (hx : x ∈ L) (h1 : ‖x‖ = 1) : ∃ w : (layerU p K L).V, uval w = x := by
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
  let y : KbarMult p := Additive.ofMul (Units.mk0 x hx0)
  have hy : y ∈ Ubar p := (mem_Ubar_iff p y).2 ((vbar_eq_zero_iff y).2 h1)
  refine ⟨⟨(⟨y, hy⟩ : Ubar p), fun g => Subtype.ext (Units.ext ?_)⟩, rfl⟩
  exact g.2 x hx

end

end ReciprocityTheory.DiscreteGroups.LocalClassField

import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.ContinuousKinv2

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConvKir

theorem sum_char_eq_zero {A : Type} [AddCommGroup A] (L L'' : AddSubgroup A)
    [Fintype (L ⧸ L''.addSubgroupOf L)] (χ : A → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y)
    (h'' : ∀ x ∈ L'', χ x = 1) (x₀ : L) (hne : χ x₀ ≠ 1) :
    ∑ q : L ⧸ L''.addSubgroupOf L, χ ((Quotient.out q : L) : A) = 0 := by
  have hterm : ∀ q : L ⧸ L''.addSubgroupOf L,
      χ ((Quotient.out ((x₀ : L ⧸ L''.addSubgroupOf L) + q) : L) : A) = χ x₀ * χ ((Quotient.out q : L) : A) := by
    intro q
    set z := Quotient.out ((x₀ : L ⧸ L''.addSubgroupOf L) + q) with hz
    have hq : ((z : L) : L ⧸ L''.addSubgroupOf L) = ((x₀ + Quotient.out q : L) : L ⧸ L''.addSubgroupOf L) := by
      rw [hz, QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    have hd := AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 hq)
    have e : (x₀ : A) + ((Quotient.out q : L) : A) = (z : A) + ((-z + (x₀ + Quotient.out q) : L) : A) := by
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
    rw [← hχ, e, hχ, h'' _ hd, mul_one]
  have hT := Equiv.sum_comp (Equiv.addLeft ((x₀ : L ⧸ L''.addSubgroupOf L))) (fun q => χ ((Quotient.out q : L) : A))
  simp only [Equiv.coe_addLeft, hterm, ← Finset.mul_sum] at hT
  have h0 : (χ x₀ - 1) * ∑ q : L ⧸ L''.addSubgroupOf L, χ ((Quotient.out q : L) : A) = 0 := by
    rw [sub_mul, hT, one_mul, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)

variable {k : Type} [Field k]

theorem psi_neg_mul (ψ : AddChar k Circle) (t : k) : ((ψ (-t) : Circle) : ℂ) * (ψ t : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem l_gU {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (ρ : Representation ℂ (GL (Fin (m + 1)) k) V) (l : Module.Dual ℂ V) (hl : IsFunctional ψ ρ l)
    (j : ℕ) (hj : j + 1 < m + 1) (g : GL (Fin (m + 1)) k) (hg : InH (j + 1) g) (x : Fin (m + 1) → k) (w : V) :
    l (ρ g (ρ (U ⟨j + 1, hj⟩ x) w)) =
      (ψ (∑ r, (if r < (⟨j + 1, hj⟩ : Fin (m + 1)) then
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ⟨j, by omega⟩ r else 0) * x r) : ℂ) * l (ρ g w) := by
  rw [← Module.End.mul_apply, ← map_mul, conj_U j hj g hg x, map_mul, Module.End.mul_apply,
    hl _ (U_mem _ _), superDiag_U]

end DiscreteGroups.sglob.LConvKir

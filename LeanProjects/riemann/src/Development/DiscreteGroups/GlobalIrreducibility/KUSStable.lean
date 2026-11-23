import Development.DiscreteGroups.GlobalIrreducibility.TopLeftElemInv

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

def chM (m : ℕ) (g : GL (Fin n) k) : ℂ := ((ψ (sdS m (g : Matrix (Fin n) (Fin n) k)) : Circle) : ℂ)

def KN (m : ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ g ∈ Nset m, ∃ v : V, w = π g v - chM ψ m g • v}

def KUS (j : ℕ) (S : Finset (Fin n)) (ξ : Fin n → k) : Submodule ℂ V :=
  Submodule.span ℂ {w | ∃ c : Fin n → k, (∀ r ∉ S, c r = 0) ∧ ∃ v : V,
    w = π (colU j c) v - ((ψ (dotj j ξ c) : Circle) : ℂ) • v}

theorem conj_apply (x g : GL (Fin n) k) (v : V) : π x (π g v) = π (x * g * x⁻¹) (π x v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

theorem KN_stable (j : ℕ) (x : GL (Fin n) k) (hx : Good j (x : Matrix (Fin n) (Fin n) k))
    (hy : Good j ((x⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) {w : V} (hw : w ∈ KN π ψ (j + 1)) :
    π x w ∈ KN π ψ (j + 1) := by
  refine (Submodule.span_le.2 ?_ : KN π ψ (j + 1) ≤ (KN π ψ (j + 1)).comap (π x)) hw
  rintro _ ⟨g, hg, v, rfl⟩
  obtain ⟨h1, h2⟩ := good_conj x hx hy hg
  refine Submodule.subset_span ⟨x * g * x⁻¹, h1, π x v, ?_⟩
  rw [map_sub, map_smul, conj_apply, chM, chM, h2]

theorem colU_comm (j : ℕ) (c d : Fin n → k) : colU j c * colU j d = colU j d * colU j c := by
  rw [← colU_add, ← colU_add, add_comm]

theorem KUS_stable (j : ℕ) (S : Finset (Fin n)) (ξ d : Fin n → k) {w : V} (hw : w ∈ KUS π ψ j S ξ) :
    π (colU j d) w ∈ KUS π ψ j S ξ := by
  refine (Submodule.span_le.2 ?_ : KUS π ψ j S ξ ≤ (KUS π ψ j S ξ).comap (π (colU j d))) hw
  rintro _ ⟨c, hc, v, rfl⟩
  refine Submodule.subset_span ⟨c, hc, π (colU j d) v, ?_⟩
  rw [map_sub, map_smul, ← Module.End.mul_apply, ← map_mul, colU_comm, map_mul, Module.End.mul_apply]

theorem W_stable (j : ℕ) (S : Finset (Fin n)) (ξ d : Fin n → k) {w : V}
    (hw : w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ) : π (colU j d) w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  rw [map_add]
  exact Submodule.add_mem_sup (KN_stable π ψ j _ (good_colU j d) (good_colU_inv j d) ha)
    (KUS_stable π ψ j S ξ d hb)

theorem KN_top (m : ℕ) (hm : n ≤ m) : KN π ψ m = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨g, hg, v, rfl⟩
  have hg1 : g = 1 := by
    ext i l
    rw [hg i l (Or.inr (by omega)), Units.val_one]
  have hs : sdS m ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg (by omega)]
  rw [hg1, chM, hs, AddChar.map_zero_eq_one, Circle.coe_one, one_smul, map_one, Module.End.one_apply, sub_self]

end DiscreteGroups.sglob.LConvGenR

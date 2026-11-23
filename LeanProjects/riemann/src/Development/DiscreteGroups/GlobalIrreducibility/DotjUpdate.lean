import Development.DiscreteGroups.GlobalIrreducibility.NeTopOfConj

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

section Dot

variable {k : Type} [Field k] {n : ℕ}

theorem dotj_add (j : ℕ) (ξ c d : Fin n → k) : dotj j ξ (c + d) = dotj j ξ c + dotj j ξ d := by
  simp only [dotj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_add]

theorem dotj_single (j : ℕ) (ξ : Fin n → k) (a : Fin n) (x : k) :
    dotj j ξ (Pi.single a x) = if a.val < j then ξ a * x else 0 := by
  rw [dotj, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem dotj_update (j : ℕ) (ξ c : Fin n → k) (a : Fin n) (x : k) (hc : c a = 0) :
    dotj j (Function.update ξ a x) c = dotj j ξ c := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = a
  · subst hi; simp [hc]
  · rw [Function.update_of_ne hi]

end Dot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem KUS_empty (j : ℕ) (ξ : Fin n → k) : KUS π ψ j ∅ ξ = ⊥ := by
  refine Submodule.span_eq_bot.2 ?_
  rintro _ ⟨c, hc, v, rfl⟩
  have : c = 0 := funext fun r => hc r (Finset.notMem_empty r)
  subst this
  have h0 : dotj j ξ (0 : Fin n → k) = 0 := Finset.sum_eq_zero fun i _ => by split_ifs <;> simp
  rw [colU_zero, h0, AddChar.map_zero_eq_one, Circle.coe_one, one_smul, map_one, Module.End.one_apply, sub_self]

theorem smooth_col (hs : IsSmooth π) (j : ℕ) (hj : j < n) (a : Fin n) (v : V) :
    ∃ s : kˣ, ∀ h ∈ ball s, π (colU j (Pi.single a h)) v = v := by
  by_cases ha : a.val < j
  · have hne : a ≠ (⟨j, hj⟩ : Fin n) := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    have hU : {g : GL (Fin n) k | π g v = v} ∈ nhds (1 : GL (Fin n) k) := (hs v).mem_nhds (by simp)
    have h0 : GlobalTheory.RootUp.elem hne (0 : k) = 1 := Units.ext (by simp [GlobalTheory.RootUp.val_elem])
    have hpre : (GlobalTheory.RootUp.elem hne) ⁻¹' {g : GL (Fin n) k | π g v = v} ∈ nhds (0 : k) :=
      (GlobalTheory.RootUp.continuous_elem hne).continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
    obtain ⟨s, hs'⟩ := exists_cball_subset hpre
    refine ⟨s, fun h hh => ?_⟩
    rw [colU_single_of_lt j hj ha]
    exact hs' hh
  · exact ⟨1, fun h _ => by rw [colU_single_of_ge j (by omega), map_one, Module.End.one_apply]⟩

end DiscreteGroups.sglob.LConvGenR

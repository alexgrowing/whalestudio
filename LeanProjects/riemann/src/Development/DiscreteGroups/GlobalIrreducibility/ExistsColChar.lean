import Development.DiscreteGroups.GlobalIrreducibility.DotjUpdate

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix DiscreteGroups.sglob.LConvGenM DiscreteGroups.sglob.LConvGenF

namespace DiscreteGroups.sglob.LConvGenR

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GL (Fin n) k) V) (ψ : AddChar k Circle)

theorem exists_col_char {c : kˣ} (hc : HasConductor ψ c) (hs : IsSmooth π) (j : ℕ) (hj : j < n)
    (h0 : KN π ψ (j + 1) ≠ ⊤) (S : Finset (Fin n)) : ∃ ξ : Fin n → k, KN π ψ (j + 1) ⊔ KUS π ψ j S ξ ≠ ⊤ := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by rw [KUS_empty, sup_bot_eq]; exact h0⟩
  | insert a S ha ih =>
    obtain ⟨ξ, hξ⟩ := ih
    let σ : k → V →ₗ[ℂ] V := fun t => π (colU j (Pi.single a t))
    have hadd : ∀ s t, σ (s + t) = σ s * σ t := fun s t => by
      simp only [σ]; rw [Pi.single_add, colU_add, map_mul]
    have hW : ∀ t, ∀ w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ, σ t w ∈ KN π ψ (j + 1) ⊔ KUS π ψ j S ξ :=
      fun t w hw => W_stable π ψ j S ξ _ hw
    obtain ⟨ξa, hξa⟩ := exists_character_sup_ne_top ψ σ hc hadd _ hW (fun v => smooth_col π hs j hj a v) hξ
    refine ⟨Function.update ξ a ξa, fun htop => hξa (eq_top_iff.2 ?_)⟩
    rw [← htop]
    refine sup_le (le_sup_left.trans le_sup_left) (Submodule.span_le.2 ?_)
    rintro _ ⟨c, hcS, v, rfl⟩
    set cS := Function.update c a 0 with hcS'
    have hcS0 : ∀ r ∉ S, cS r = 0 := by
      intro r hr
      by_cases hra : r = a
      · subst hra; simp [cS]
      · rw [hcS', Function.update_of_ne hra]; exact hcS r (by simp [hra, hr])
    have hsplit : c = Pi.single a (c a) + cS := by
      funext r
      by_cases hra : r = a
      · subst hra; simp [cS]
      · simp [cS, hra, Pi.single_apply]
    have hdot : dotj j (Function.update ξ a ξa) c =
        dotj j (Function.update ξ a ξa) (Pi.single a (c a)) + dotj j ξ cS := by
      conv_lhs => rw [hsplit]
      rw [dotj_add, dotj_update j ξ cS a ξa (by simp [cS])]
    have e : π (colU j c) v - ((ψ (dotj j (Function.update ξ a ξa) c) : Circle) : ℂ) • v =
        σ (c a) (π (colU j cS) v - ((ψ (dotj j ξ cS) : Circle) : ℂ) • v) +
        ((ψ (dotj j ξ cS) : Circle) : ℂ) • (σ (c a) v -
          ((ψ (dotj j (Function.update ξ a ξa) (Pi.single a (c a))) : Circle) : ℂ) • v) := by
      have hcol : π (colU j c) v = σ (c a) (π (colU j cS) v) := by
        conv_lhs => rw [hsplit]
        rw [colU_add, map_mul, Module.End.mul_apply]
      rw [hcol, hdot, AddChar.map_add_eq_mul, Circle.coe_mul, map_sub, map_smul, smul_sub, smul_smul,
        mul_comm ((ψ (dotj j (Function.update ξ a ξa) (Pi.single a (c a))) : Circle) : ℂ)]
      abel
    show _ ∈ _
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hW _ _ (Submodule.mem_sup_right
      (Submodule.subset_span ⟨cS, hcS0, v, rfl⟩)))) (Submodule.smul_mem _ _ ?_)
    rw [dotj_single]
    by_cases haj : a.val < j
    · rw [if_pos haj, Function.update_self]
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨c a, v, rfl⟩)
    · rw [if_neg haj, AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
      simp only [σ]
      rw [colU_single_of_ge j (by omega), map_one, Module.End.one_apply, sub_self]
      exact Submodule.zero_mem _

end DiscreteGroups.sglob.LConvGenR

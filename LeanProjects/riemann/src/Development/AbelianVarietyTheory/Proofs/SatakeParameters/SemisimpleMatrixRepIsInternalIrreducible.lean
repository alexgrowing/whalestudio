import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SemisimpleDecomp

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

theorem isInv_inf {ρ : Γ →* GL (Fin a) k} {U V : Submodule k (Fin a → k)} (hU : IsInv ρ U)
    (hV : IsInv ρ V) : IsInv ρ (U ⊓ V) :=
  fun g v hv => ⟨hU g v hv.1, hV g v hv.2⟩

theorem isInv_top (ρ : Γ →* GL (Fin a) k) : IsInv ρ ⊤ := fun _ _ _ => Submodule.mem_top

theorem exists_irr_le {ρ : Γ →* GL (Fin a) k} {U : Submodule k (Fin a → k)} (hU : IsInv ρ U)
    (h0 : U ≠ ⊥) : ∃ W, W ≤ U ∧ IsIrrSub ρ W := by
  obtain ⟨W, ⟨hW0, hWi, hWU⟩, hmin⟩ := (wellFounded_lt (α := Submodule k (Fin a → k))).has_min
    {W | W ≠ ⊥ ∧ IsInv ρ W ∧ W ≤ U} ⟨U, h0, hU, le_rfl⟩
  refine ⟨W, hWU, hW0, hWi, fun W' hle hi => ?_⟩
  by_cases h : W' = ⊥
  · exact Or.inl h
  · right
    by_contra hne
    exact hmin W' ⟨h, hi, hle.trans hWU⟩ (lt_of_le_of_ne hle hne)

theorem disjoint_sup_of_le {α : Type*} [Lattice α] [OrderBot α] [IsModularLattice α] {x b c w : α}
    (hx : x ≤ c) (hb : b ≤ c) (hxb : Disjoint x b) (hw : Disjoint w c) : Disjoint x (w ⊔ b) := by
  have hc : (b ⊔ w) ⊓ c = b := by
    rw [sup_inf_assoc_of_le w hb, hw.eq_bot, sup_bot_eq]
  rw [disjoint_iff_inf_le]
  calc x ⊓ (w ⊔ b) ≤ x ⊓ b := by
        refine le_inf inf_le_left ?_
        exact (le_inf (inf_le_right.trans (sup_comm w b).le) (inf_le_left.trans hx)).trans hc.le
    _ ≤ ⊥ := hxb.le_bot

theorem exists_decomp {ρ : Γ →* GL (Fin a) k} (hρ : IsSSRep ρ) (U : Submodule k (Fin a → k))
    (hU : IsInv ρ U) : ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)),
      iSupIndep Vs ∧ iSup Vs = U ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  induction U using WellFoundedLT.induction with
  | _ U ih =>
  by_cases h0 : U = ⊥
  · exact ⟨0, Fin.elim0, fun i => i.elim0, by simp [h0], fun j => j.elim0⟩
  obtain ⟨W, hWU, hW⟩ := exists_irr_le hU h0
  obtain ⟨W', hW'i, hc⟩ := hρ W hW.2.1
  have hlt : U ⊓ W' < U := by
    refine lt_of_le_of_ne inf_le_left fun heq => hW.1 ?_
    have hle : W ≤ W' := hWU.trans (heq.symm ▸ inf_le_right)
    exact hc.disjoint.eq_bot_of_le hle
  obtain ⟨n, Vs, hind, hsup, hirr⟩ := ih _ hlt (isInv_inf hU hW'i)
  have hVs : ∀ j, Vs j ≤ U ⊓ W' := fun j => hsup ▸ le_iSup Vs j
  refine ⟨n + 1, Fin.cons W Vs, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · refine hc.disjoint.mono_right (iSup₂_le fun j hj => ?_)
      refine Fin.cases (fun h => absurd rfl h) (fun j _ => ?_) j hj
      simpa using (hVs j).trans inf_le_right
    · have hle : (⨆ (j) (_ : j ≠ Fin.succ i), (Fin.cons W Vs : Fin (n + 1) → _) j) ≤
          W ⊔ ⨆ (j) (_ : j ≠ i), Vs j := by
        refine iSup₂_le fun j hj => ?_
        refine Fin.cases (fun _ => ?_) (fun j hj => ?_) j hj
        · simp
        · have hji : j ≠ i := fun h => hj (h ▸ rfl)
          simp only [Fin.cons_succ]
          exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ≠ i) => Vs j) j hji)
      simp only [Fin.cons_succ]
      refine (disjoint_sup_of_le (hVs i) (iSup₂_le fun j _ => hVs j) (hind i)
        (hc.disjoint.mono_right inf_le_right)).mono_right hle
  · have hS : iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) = W ⊔ iSup Vs := by
      refine le_antisymm (iSup_le fun j => ?_) (sup_le ?_ (iSup_le fun j => ?_))
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp
        · simpa using le_sup_of_le_right (le_iSup Vs j)
      · simpa using le_iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) 0
      · simpa using le_iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) j.succ
    rw [hS, hsup, inf_comm, ← sup_inf_assoc_of_le W' hWU, hc.sup_eq_top, top_inf_eq]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hW
    · simpa using hirr j

end GlobalTheory.SemisimpleDecomp

theorem GlobalTheory.semisimple_matrix_rep_decomp : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ}
    (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)),
      DirectSum.IsInternal Vs ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  intro k Γ _ _ a ρ hρ
  obtain ⟨n, Vs, hind, hsup, hirr⟩ :=
    GlobalTheory.SemisimpleDecomp.exists_decomp hρ ⊤ (GlobalTheory.SemisimpleDecomp.isInv_top ρ)
  exact ⟨n, Vs, (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Vs).2 ⟨hind, hsup⟩,
    hirr⟩

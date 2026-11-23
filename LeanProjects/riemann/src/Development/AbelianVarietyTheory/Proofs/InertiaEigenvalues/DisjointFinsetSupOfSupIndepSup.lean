import Mathlib

namespace GlobalTheory

theorem disjoint_finset_sup_of_supIndep_sup :
    ∀ (R V ι : Type) [Ring R] [AddCommGroup V] [Module R V] (F : Finset ι) (G B : ι → Submodule R V),
      F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) →
        Disjoint (F.sup G) (F.sup B) := by
  intro R V ι _ _ _ F G B hind hdis
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : s.SupIndep (fun i => G i ⊔ B i) := hind.subset (Finset.subset_insert _ _)
    have ih' := ih hs (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
    have hA : Disjoint (G a ⊔ B a) (s.sup fun i => G i ⊔ B i) :=
      hind (Finset.subset_insert a s) (Finset.mem_insert_self a s) ha
    have hGs : s.sup G ≤ s.sup (fun i => G i ⊔ B i) := Finset.sup_mono_fun (fun i _ => le_sup_left)
    have hBs : s.sup B ≤ s.sup (fun i => G i ⊔ B i) := Finset.sup_mono_fun (fun i _ => le_sup_right)
    rw [Finset.sup_insert, Finset.sup_insert, Submodule.disjoint_def]
    intro x hxG hxB
    obtain ⟨g, hg, g', hg', rfl⟩ := Submodule.mem_sup.mp hxG
    obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.mp hxB
    have h1 : g - b ∈ G a ⊔ B a := Submodule.sub_mem _ (Submodule.mem_sup_left hg) (Submodule.mem_sup_right hb)
    have h2 : g - b ∈ s.sup (fun i => G i ⊔ B i) := by
      have : g - b = b' - g' := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm b' b, hbb]
      rw [this]
      exact Submodule.sub_mem _ (hBs hb') (hGs hg')
    have h3 : g - b = 0 := (Submodule.disjoint_def.mp hA) _ h1 h2
    have hgb : g = b := sub_eq_zero.mp h3
    have hg0 : g = 0 := (Submodule.disjoint_def.mp (hdis a (Finset.mem_insert_self a s))) g hg (hgb ▸ hb)
    have hg'b' : g' = b' := by
      subst hgb
      exact add_left_cancel hbb.symm
    have hg'0 : g' = 0 := (Submodule.disjoint_def.mp ih') g' hg' (hg'b' ▸ hb')
    rw [hg0, hg'0, add_zero]

end GlobalTheory

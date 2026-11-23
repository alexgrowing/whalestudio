import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.UniSeqBasic

theorem perm_lift {α β : Type} (f : α → β) {l l' : List β} (h : l.Perm l') :
    ∀ γ : List α, γ.map f = l → ∃ γ' : List α, γ.Perm γ' ∧ γ'.map f = l' := by
  induction h with
  | nil => intro γ hγ; exact ⟨γ, List.Perm.refl _, hγ⟩
  | cons x _ ih =>
    intro γ hγ
    rcases γ with _ | ⟨a, γ⟩
    · simp at hγ
    · simp only [List.map_cons, List.cons.injEq] at hγ
      obtain ⟨γ', h1, h2⟩ := ih γ hγ.2
      exact ⟨a :: γ', h1.cons a, by simp [h2, hγ.1]⟩
  | swap x y l =>
    intro γ hγ
    rcases γ with _ | ⟨a, _ | ⟨b, γ⟩⟩
    · simp at hγ
    · simp at hγ
    · simp only [List.map_cons, List.cons.injEq] at hγ
      exact ⟨b :: a :: γ, List.Perm.swap _ _ _, by simp [hγ.1, hγ.2.1, hγ.2.2]⟩
  | trans _ _ ih1 ih2 =>
    intro γ hγ
    obtain ⟨γ1, p1, e1⟩ := ih1 γ hγ
    obtain ⟨γ2, p2, e2⟩ := ih2 γ1 e1
    exact ⟨γ2, p1.trans p2, e2⟩

def Orth (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (a b : M × (M →ₗ[R] R)) : Prop := a.2 b.1 = 0 ∧ b.2 a.1 = 0

theorem orth_symm (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    Symmetric (Orth R M) := fun _ _ h => ⟨h.2, h.1⟩

theorem mem_uniM_iff (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (l : List M) :
    l ∈ uniM R M ↔ ∃ γ : List (M × (M →ₗ[R] R)), γ.map Prod.fst = l ∧
      (∀ p ∈ γ, p.2 p.1 = 1) ∧ γ.Pairwise (Orth R M) := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(List.finRange l.length).map (fun i => (l.get i, f i)), ?_, ?_, ?_⟩
    · apply List.ext_getElem <;> simp
    · intro p hp
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hp
      simpa using hf i i
    · rw [List.pairwise_map]
      refine (List.pairwise_lt_finRange l.length).imp fun {i j} hij => ?_
      have hne : i ≠ j := ne_of_lt hij
      exact ⟨by simpa [hne] using hf i j, by simpa [hne.symm] using hf j i⟩
  · rintro ⟨γ, rfl, hone, hpw⟩
    refine ⟨fun i => (γ[i.1]'(by simpa using i.2)).2, fun i j => ?_⟩
    have hi : i.1 < γ.length := by simpa using i.2
    have hj : j.1 < γ.length := by simpa using j.2
    rw [List.pairwise_iff_getElem] at hpw
    simp only [List.get_eq_getElem, List.getElem_map]
    split_ifs with hij
    · subst hij
      exact hone _ (List.getElem_mem _)
    · rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
      · exact (hpw _ _ hi hj h).1
      · exact (hpw _ _ hj hi h).2

theorem main : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], SubClosed (uniM R M) ∧ (∀ l l' : List M, l.Perm l' → l ∈ uniM R M → l' ∈ uniM R M) ∧ ∀ (ψ : M ≃ₗ[R] M) (l : List M), l.map ψ ∈ uniM R M ↔ l ∈ uniM R M := by
  intro R M _ _ _
  have key : ∀ (ψ : M ≃ₗ[R] M) (l : List M), l ∈ uniM R M → l.map ψ ∈ uniM R M := by
    intro ψ l hl
    obtain ⟨γ, rfl, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    refine (mem_uniM_iff R M _).mpr
      ⟨γ.map (fun p => (ψ p.1, p.2 ∘ₗ (ψ.symm : M →ₗ[R] M))), ?_, ?_, ?_⟩
    · simp [List.map_map, Function.comp_def]
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      simpa using hone q hq
    · rw [List.pairwise_map]
      refine hpw.imp fun {a b} h => ?_
      simpa [Orth] using h
  refine ⟨?_, ?_, ?_⟩
  · intro l hl l' hsub
    obtain ⟨γ, rfl, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    obtain ⟨γ', hγ', rfl⟩ := List.sublist_map_iff.mp hsub
    exact (mem_uniM_iff R M _).mpr ⟨γ', rfl, fun p hp => hone p (hγ'.subset hp), hpw.sublist hγ'⟩
  · intro l l' hperm hl
    obtain ⟨γ, hγ, hone, hpw⟩ := (mem_uniM_iff R M l).mp hl
    obtain ⟨γ', hp, hm⟩ := perm_lift Prod.fst hperm γ hγ
    exact (mem_uniM_iff R M _).mpr
      ⟨γ', hm, fun p hq => hone p (hp.symm.subset hq), hpw.perm hp (fun {_ _} h => orth_symm R M h)⟩
  · intro ψ l
    constructor
    · intro h
      have := key ψ.symm _ h
      simpa [List.map_map, Function.comp_def] using this
    · exact key ψ l

end GlobalTheory.UniSeqBasic

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.subClosed_and_perm_and_linearEquiv_invariant_uniM : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], SubClosed (uniM R M) ∧ (∀ l l' : List M, l.Perm l' → l ∈ uniM R M → l' ∈ uniM R M) ∧ ∀ (ψ : M ≃ₗ[R] M) (l : List M), l.map ψ ∈ uniM R M ↔ l ∈ uniM R M := by
  first
  | exact @GlobalTheory.UniSeqBasic.main
  | exact @GlobalTheory.UniSeqBasic.mem_uniM_iff
  | exact @GlobalTheory.UniSeqBasic.orth_symm
  | exact @GlobalTheory.UniSeqBasic.perm_lift
end

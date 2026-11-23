import Mathlib

namespace GlobalTheory

open Finset

theorem sum_piFinset_fin_succ_cons {α K : Type} [AddCommMonoid K] (n : ℕ) (S : Finset α)
    (F : (Fin (n + 1) → α) → K) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S), F t =
      ∑ a ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) := by
  rw [← Finset.sum_product' S (Fintype.piFinset (fun _ : Fin n => S))
    (fun a t => F (Fin.cons a t))]
  symm
  refine Finset.sum_equiv (Fin.consEquiv (fun _ => α)) ?_ ?_
  · rintro ⟨a, t⟩
    simp [Fin.forall_fin_succ, Fin.consEquiv]
  · rintro ⟨a, t⟩ _
    rfl

theorem weighted_sum_piFinset_fin {α K : Type} [CommRing K] (G : (α → K) → Prop)
    (S S' : Finset α) (w w' : K)
    (h : ∀ f, G f → w * ∑ a ∈ S, f a = w' * ∑ a ∈ S', f a) (n : ℕ) :
    ∀ F : (Fin n → α) → K, (∀ (t : Fin n → α) (i : Fin n), G (fun a => F (Function.update t i a))) →
      w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F t =
        w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F t := by
  induction n with
  | zero => intro F _; simp
  | succ n ih =>
    intro F hF
    have h1 : ∀ a : α, w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) =
        w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F (Fin.cons a t) := by
      intro a
      refine ih (fun t => F (Fin.cons a t)) ?_
      intro t i
      have := hF (Fin.cons a t) i.succ
      simpa only [← Fin.cons_update] using this
    have h2 : ∀ t : Fin n → α, w * ∑ a ∈ S, F (Fin.cons a t) =
        w' * ∑ a ∈ S', F (Fin.cons a t) := by
      intro t
      rcases isEmpty_or_nonempty α with hα | ⟨⟨a0⟩⟩
      · simp [Finset.eq_empty_of_isEmpty S, Finset.eq_empty_of_isEmpty S']
      · refine h _ ?_
        have := hF (Fin.cons a0 t) 0
        simpa only [Fin.update_cons_zero] using this
    rw [sum_piFinset_fin_succ_cons, sum_piFinset_fin_succ_cons]
    calc w ^ (n + 1) * ∑ a ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t)
        = w * ∑ a ∈ S, w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) := by
          rw [← Finset.mul_sum]; ring
      _ = w * ∑ a ∈ S, w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F (Fin.cons a t) := by
          simp only [h1]
      _ = w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), w * ∑ a ∈ S, F (Fin.cons a t) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]; ring
      _ = w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), w' * ∑ a ∈ S', F (Fin.cons a t) := by
          simp only [h2]
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_comm]; ring

theorem weighted_sum_piFinset : ∀ (ι α K : Type) [Fintype ι] [DecidableEq ι] [CommRing K] (G : (α → K) → Prop) (S S' : Finset α) (w w' : K), (∀ f, G f → w * ∑ a ∈ S, f a = w' * ∑ a ∈ S', f a) → ∀ F : (ι → α) → K, (∀ (t : ι → α) (i : ι), G (fun a => F (Function.update t i a))) → w ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S), F t = w' ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S'), F t := by
  intro ι α K _ _ _ G S S' w w' h F hF
  let e := Fintype.equivFin ι
  have key : ∀ T : Finset α, ∑ t ∈ Fintype.piFinset (fun _ : ι => T), F t =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin (Fintype.card ι) => T), F (t ∘ e) := by
    intro T
    symm
    refine Finset.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl α)) ?_ ?_
    · intro t
      simp only [Fintype.mem_piFinset, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl,
        Function.comp, id]
      exact ⟨fun H i => H _, fun H i => by simpa using H (e.symm i)⟩
    · intro t _
      rfl
  rw [key, key]
  refine weighted_sum_piFinset_fin G S S' w w' h _ (fun t => F (t ∘ e)) ?_
  intro t i
  simp only [Function.update_comp_equiv]
  exact hF _ _

end GlobalTheory

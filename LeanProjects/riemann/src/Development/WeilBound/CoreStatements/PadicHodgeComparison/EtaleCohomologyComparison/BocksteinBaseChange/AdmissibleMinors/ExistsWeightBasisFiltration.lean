import Mathlib

namespace CrystallineSemistableComparison.Inj

open Submodule

theorem exists_weight_basis_filtration {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (F : ℕ → Set H) (N : ℕ) (hN : ∀ j, N ≤ j → ∀ x ∈ F j, x = 0) :
    ∀ i, ∃ (s : Set H) (w : H → ℕ), LinearIndepOn K id s ∧
      (∀ v ∈ s, v ∈ F (w v) ∧ N - i ≤ w v) ∧
      ∀ j, N - i ≤ j → F j ⊆ span K {v | v ∈ s ∧ j ≤ w v} := by
  intro i
  induction i with
  | zero =>
    refine ⟨∅, fun _ => 0, linearIndepOn_empty K id, by simp, ?_⟩
    intro j hj x hx
    rw [hN j (by omega) x hx]
    exact zero_mem _
  | succ i ih =>
    obtain ⟨s, w, hli, hs, hspan⟩ := ih
    by_cases hi : N - (i + 1) = N - i
    · exact ⟨s, w, hli, fun v hv => by rw [hi]; exact hs v hv, fun j hj => hspan j (hi ▸ hj)⟩
    obtain ⟨b, hbt, hsb, htb, hlib⟩ :=
      exists_linearIndepOn_extension hli (Set.subset_union_left : s ⊆ s ∪ F (N - (i + 1)))
    classical
    refine ⟨b, fun v => if v ∈ s then w v else N - (i + 1), hlib, ?_, ?_⟩
    · intro v hv
      by_cases h : v ∈ s
      · simp only [h, if_true]
        exact ⟨(hs v h).1, by have := (hs v h).2; omega⟩
      · simp only [h, if_false]
        refine ⟨?_, le_rfl⟩
        rcases hbt hv with h' | h'
        · exact absurd h' h
        · exact h'
    · intro j hj
      rcases Nat.eq_or_lt_of_le hj with hjk | hlt
      · subst hjk
        intro x hx
        have hx' : x ∈ span K (id '' b) := htb ⟨x, Or.inr hx, rfl⟩
        rw [Set.image_id] at hx'
        refine span_mono ?_ hx'
        intro v hv
        refine ⟨hv, ?_⟩
        by_cases h : v ∈ s
        · simp only [h, if_true]
          have := (hs v h).2
          omega
        · simp [h]
      · have hj' : N - i ≤ j := by omega
        refine (hspan j hj').trans (span_mono ?_)
        rintro v ⟨hv, hw⟩
        exact ⟨hsb hv, by simp [hv, hw]⟩

theorem wt_basis {K H : Type*} [Field K] [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (F : ℕ → Set H) (hF : Antitone F) (h0 : F 0 = Set.univ) (N : ℕ) (hN : ∀ x ∈ F N, x = 0) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) K H) (w : Fin m → ℕ),
      ∀ s, b s ∈ F (w s) ∧ ∀ x ∈ F (w s + 1), b.coord s x = 0 := by
  obtain ⟨s, w, hli, hs, hspan⟩ := exists_weight_basis_filtration (K := K) F N (fun j hj x hx => hN x (hF hj hx)) N
  have hli' : LinearIndependent K ((↑) : s → H) := hli
  have htop : ⊤ ≤ span K (Set.range ((↑) : s → H)) := by
    rw [Subtype.range_coe]
    intro x _
    have := hspan 0 (by omega) (h0 ▸ Set.mem_univ x)
    exact span_mono (fun v hv => hv.1) this
  let b0 := Module.Basis.mk hli' htop
  have hb0 : ∀ v, b0 v = (v : H) := fun v => Module.Basis.mk_apply hli' htop v
  have : Finite s := Module.Finite.finite_basis b0
  haveI : Fintype s := Fintype.ofFinite s
  let e := Fintype.equivFin s
  refine ⟨Fintype.card s, b0.reindex e, fun t => w (e.symm t), fun t => ⟨?_, ?_⟩⟩
  · rw [Module.Basis.reindex_apply, hb0]
    exact (hs _ (e.symm t).2).1
  · intro x hx
    rw [Module.Basis.coord_apply, Module.Basis.repr_reindex_apply]
    have hx' := hspan (w (e.symm t) + 1) (by omega) hx
    have himg : {v | v ∈ s ∧ w (e.symm t) + 1 ≤ w v} = b0 '' {u : s | w (e.symm t) + 1 ≤ w u} := by
      ext v
      constructor
      · rintro ⟨hv, hw⟩
        exact ⟨⟨v, hv⟩, hw, hb0 _⟩
      · rintro ⟨u, hu, rfl⟩
        rw [hb0]
        exact ⟨u.2, hu⟩
    rw [himg, SetLike.mem_coe, Module.Basis.mem_span_image] at hx'
    by_contra hne
    have := hx' (Finsupp.mem_support_iff.mpr hne)
    simp at this

end CrystallineSemistableComparison.Inj

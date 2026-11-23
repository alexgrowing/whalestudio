import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ColumnAntisymmetry

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def npairs {m : ℕ} (col : Fin m → ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin m × Fin m => x.1 < x.2 ∧ col x.1 = col x.2).card

def ColInj {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) : Prop :=
  ∀ p q, col p = col q → I p = I q → p = q

def rk {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) (p : Fin m) : ℕ :=
  (Finset.univ.filter fun q => col q = col p ∧ I p < I q).card

theorem rk_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (I : Fin m → Fin n)
    (hI : ColInj col I) (p : Fin m) : rk col I p ≤ (top : ℕ) - I p := by
  unfold rk
  have h1 : (Finset.univ.filter fun q => col q = col p ∧ I p < I q).card ≤ (Finset.Ioi (I p)).card := by
    apply Finset.card_le_card_of_injOn I
    · intro q hq
      simp at hq ⊢
      exact hq.2
    · intro q hq q' hq' hqq
      simp at hq hq'
      exact hI q q' (hq.1.trans hq'.1.symm) hqq
  rw [Fin.card_Ioi] at h1
  omega

theorem sum_rk {m : ℕ} (col : Fin m → ℕ) (I : Fin m → Fin n) (hI : ColInj col I) :
    ∑ p, rk col I p = npairs col := by
  have e1 : ∑ p, rk col I p = (Finset.univ.filter fun x : Fin m × Fin m => col x.2 = col x.1 ∧ I x.1 < I x.2).card := by
    unfold rk
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [e1]
  unfold npairs
  apply Finset.card_bij' (fun x _ => if x.1 < x.2 then x else x.swap) (fun y _ => if I y.1 < I y.2 then y else y.swap)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_cases h : x.1 < x.2
    · simp [h, hx.2]
    · have h' : ¬ I x.2 < I x.1 := not_lt.mpr hx.2.le
      simp [h, h']
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    by_cases h : I y.1 < I y.2
    · simp [h, hy.1]
    · have h' : ¬ y.2 < y.1 := not_lt.mpr hy.1.le
      simp [h, h']
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have hne : x.1 ≠ x.2 := fun h => by rw [h] at hx; exact lt_irrefl _ hx.2
    split_ifs with h
    · exact ⟨h, hx.1.symm⟩
    · try simp only [Prod.fst_swap, Prod.snd_swap]
      refine ⟨?_, hx.1⟩
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd h' h
      · exact h'
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hne : I y.1 ≠ I y.2 := fun h => (ne_of_lt hy.1) (hI _ _ hy.2 h)
    split_ifs with h
    · exact ⟨hy.2.symm, h⟩
    · try simp only [Prod.fst_swap, Prod.snd_swap]
      exact ⟨hy.2, lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)⟩

theorem npairs_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (I : Fin m → Fin n)
    (hI : ColInj col I) : npairs col ≤ ∑ p, ((top : ℕ) - I p) := by
  rw [← sum_rk col I hI]
  exact Finset.sum_le_sum fun p _ => rk_le col top htop I hI p

theorem eq_of_le {m : ℕ} (col : Fin m → ℕ) (top : Fin n) (htop : (top : ℕ) + 1 = n) (b I : Fin m → Fin n)
    (hb : IsTab col b) (hI : ColInj col I) (h : ∑ p, ((top : ℕ) - I p) ≤ npairs col) :
    ∃ σ ∈ colG col, I = b ∘ σ := by
  classical
  have heq : ∀ p, rk col I p = (top : ℕ) - I p := by
    have hs : ∑ p, rk col I p = ∑ p, ((top : ℕ) - I p) :=
      le_antisymm (by rw [sum_rk col I hI]; exact npairs_le col top htop I hI) (by rw [sum_rk col I hI]; exact h)
    intro p
    exact (Finset.sum_eq_sum_iff_of_le (fun p _ => rk_le col top htop I hI p)).mp hs p (Finset.mem_univ p)
  have hex : ∀ p, ∃ q, col q = col p ∧ b q = I p := by
    intro p
    have hA : (top : ℕ) - I p + 1 ≤ (Finset.univ.filter fun q => col q = col p).card := by
      rw [← heq p]
      unfold rk
      rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun q => col q = col p ∧ I p < I q) (a := p) (by simp)]
      apply Finset.card_le_card
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rcases hq with rfl | hq
      · rfl
      · exact hq.1
    by_cases hb0 : ∃ q, col q = col p ∧ b q ≤ I p
    · obtain ⟨q0, hq0c, hq0b⟩ := hb0
      rcases lt_or_eq_of_le hq0b with hlt | heq'
      · obtain ⟨q, hqc, hqb⟩ := hb.2 q0 (I p) hlt
        exact ⟨q, hqc.trans hq0c, hqb⟩
      · exact ⟨q0, hq0c, heq'⟩
    · push_neg at hb0
      exfalso
      have hB : (Finset.univ.filter fun q => col q = col p).card ≤ (Finset.Ioi (I p)).card := by
        apply Finset.card_le_card_of_injOn b
        · intro q hq
          simp at hq ⊢
          exact hb0 q hq
        · intro q hq q' hq' hqq
          simp at hq hq'
          exact hb.1 q q' (hq.trans hq'.symm) hqq
      rw [Fin.card_Ioi] at hB
      have := (I p).isLt
      omega
  choose σf hσc hσb using hex
  have hinj : Function.Injective σf := by
    intro p p' hpp
    have hc : col p = col p' := by rw [← hσc p, ← hσc p', hpp]
    have hi : I p = I p' := by rw [← hσb p, ← hσb p', hpp]
    exact hI p p' hc hi
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective σf (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ?_, ?_⟩
  · simp [colG, σ, hσc]
  · funext p
    simp [σ, hσb]

end ColumnAntisymmetry

end PositivityTheory.Rg.Cz

end

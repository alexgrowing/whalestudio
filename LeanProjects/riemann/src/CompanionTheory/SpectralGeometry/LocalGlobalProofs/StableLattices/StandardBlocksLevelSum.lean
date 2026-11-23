import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem card_lev_lt_succ {n : ℕ} (lev : Fin n → ℕ) (k : ℕ) :
    (univ.filter fun a => lev a < k + 1).card =
      (univ.filter fun a => lev a < k).card + (univ.filter fun a => lev a = k).card := by
  have hd : Disjoint (univ.filter fun a => lev a < k) (univ.filter fun a => lev a = k) := by
    refine Finset.disjoint_left.2 fun a ha hb => ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    omega
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and, mem_union]
  omega

theorem sum_sz_castLE {n M : ℕ} (lev : Fin n → ℕ) : ∀ (k : ℕ) (hk : k ≤ M),
    ∑ b : Fin k, sz lev M (Fin.castLE hk b) = (univ.filter fun a => lev a < k).card := by
  intro k
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    rw [Fin.sum_univ_castSucc, card_lev_lt_succ, ← ih (by omega)]
    rfl

theorem lt_card_iff {n : ℕ} {lev : Fin n → ℕ} (hm : Monotone lev) (k : ℕ) (a : Fin n) :
    (a : ℕ) < (univ.filter fun b => lev b < k).card ↔ lev a < k := by
  constructor
  · intro h
    by_contra hn
    have hs : (univ.filter fun b => lev b < k) ⊆ Finset.Iio a := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      exact Finset.mem_Iio.2 (hm.reflect_lt (by omega))
    have := Finset.card_le_card hs
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have hs : Finset.Iic a ⊆ (univ.filter fun b => lev b < k) := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and]
      exact lt_of_le_of_lt (hm (Finset.mem_Iic.1 hb)) h
    have := Finset.card_le_card hs
    rw [Fin.card_Iic] at this
    omega

theorem lev_stdBlocks {n M : ℕ} (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev)
    (i : Fin M) (p : Fin (sz lev M i)) : lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ) := by
  have hv := stdBlocks_val (sz lev M) h i p
  rw [sum_sz_castLE lev (i : ℕ) i.2.le] at hv
  have hp : (p : ℕ) < (univ.filter fun a => lev a = (i : ℕ)).card := p.2
  have h1 := lt_card_iff hm (i : ℕ) (stdBlocks (sz lev M) h ⟨i, p⟩)
  have h2 := lt_card_iff hm ((i : ℕ) + 1) (stdBlocks (sz lev M) h ⟨i, p⟩)
  rw [card_lev_lt_succ] at h2
  have h3 := h2.1 (by omega)
  have h4 : ¬ lev (stdBlocks (sz lev M) h ⟨i, p⟩) < (i : ℕ) := fun hl => by
    have := h1.2 hl
    omega
  omega

theorem stdBlocks_clusters : ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    (∀ (i : Fin M) (p : Fin (sz lev M i)), lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ)) ∧
    ∀ (f : Fin n → ℂ) (i : Fin M), ∑ p : Fin (sz lev M i), f (stdBlocks (sz lev M) h ⟨i, p⟩) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), f a := by
  intro n M lev h hm _
  refine ⟨lev_stdBlocks lev h hm, fun f i => ?_⟩
  refine Finset.sum_bij (fun p _ => stdBlocks (sz lev M) h ⟨i, p⟩) ?_ ?_ ?_ ?_
  · intro p _
    simp only [mem_filter, mem_univ, true_and]
    exact lev_stdBlocks lev h hm i p
  · intro p _ q _ hpq
    have := (stdBlocks (sz lev M) h).injective hpq
    simpa using this
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    obtain ⟨⟨j, q⟩, rfl⟩ := (stdBlocks (sz lev M) h).surjective a
    have hj : j = i := Fin.ext ((lev_stdBlocks lev h hm j q).symm.trans ha)
    subst hj
    exact ⟨q, mem_univ _, rfl⟩
  · intro p _
    rfl

end GlobalTheory.CompanionTheory.RgCOBlock

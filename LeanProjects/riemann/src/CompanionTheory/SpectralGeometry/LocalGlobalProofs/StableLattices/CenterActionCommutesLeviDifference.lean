import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy

noncomputable section

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

theorem ev_fa {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (Y : ℂ) :
    ev E (fa n Y) = qdet E (Y + ((n : ℂ) - 1) / 2) := by
  unfold fa
  rw [map_qdet]
  congr 1
  funext p q
  simp [ev]

theorem evL_fb {n M : ℕ} (lev : Fin n → ℕ) (d : Fin M → ℕ) (h : ∑ i, d i = n)
    (hlev : ∀ (i : Fin M) (p : Fin (d i)), lev (stdBlocks d h ⟨i, p⟩) = (i : ℕ))
    {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (Y : ℂ) :
    evL lev E (fb d h Y) = (List.ofFn fun i : Fin M =>
      qdet (fun p q : Fin (d i) => E (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩))
        (Y + ((d i : ℂ) - 1) / 2 - (modExp (fun i => Fin (d i)) i : ℂ) / 2)).prod := by
  unfold fb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp]
  rw [map_qdet, shift, add_sub_assoc]
  congr 1
  funext p q
  simp [evL, hlev]

theorem span_apply_sum {n : ℕ} (lev : Fin n → ℕ) (hm : Monotone lev) {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (r : Fin n → Fin n → Prop) (hr : ∀ p q, r p q → lev p < lev q)
    {y : Module.End ℂ V}
    (hy : y ∈ Submodule.span ℂ {y : Module.End ℂ V | ∃ (p q : Fin n) (w : Module.End ℂ V), r p q ∧ y = E p q * w})
    (x : V) : ∃ w : Pos n → V, y x = ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, q, w, hpq, rfl⟩ := hy
    have hl := hr p q hpq
    have hlt : p < q := by
      by_contra hc
      exact absurd (hm (not_lt.mp hc)) (not_le.mpr hl)
    classical
    refine ⟨Pi.single (⟨(p, q), hlt⟩ : Pos n) (w x), ?_⟩
    rw [Finset.sum_eq_single (⟨(p, q), hlt⟩ : Pos n)]
    · simp [inU, hl]
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu⟩ := ha
    obtain ⟨v, hv⟩ := hb
    refine ⟨u + v, ?_⟩
    rw [LinearMap.add_apply, hu, hv, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  | smul c a _ ha =>
    obtain ⟨u, hu⟩ := ha
    refine ⟨c • u, ?_⟩
    rw [LinearMap.smul_apply, hu, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp

theorem co_hyp : ∀ (n M : ℕ) (lev : Fin n → ℕ) (d : Fin M → ℕ) (h : ∑ i, d i = n) (Y : ℂ), Monotone lev →
    (∀ (i : Fin M) (p : Fin (d i)), lev (stdBlocks d h ⟨i, p⟩) = (i : ℕ)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
      (∀ i : Pos n, inU lev i → Commute (E i.1.1 i.1.2) (ev E (fa n Y))) ∧
      ∀ x : V, ∃ w : Pos n → V, ev E (fa n Y) x - evL lev E (fb d h Y) x =
        ∑ i : Pos n, if inU lev i then E i.1.1 i.1.2 (w i) else 0 := by
  intro n M lev d h Y hm hlev V _ _ E hE
  rw [ev_fa, evL_fb lev d h hlev]
  refine ⟨fun i _ => (Formalism.REAL.qDetCentral (Module.End ℂ V) n E hE _ i.1.1 i.1.2).symm, fun x => ?_⟩
  have hlevb : ∀ p : Fin n, lev p = ((blk (stdBlocks d h) p : Fin M) : ℕ) := by
    intro p
    have := hlev ((stdBlocks d h).symm p).1 ((stdBlocks d h).symm p).2
    simpa [blk] using this
  have hc := GlobalTheory.CapHC.qdet_blocks_congr (Module.End ℂ V) d h E hE Y
  obtain ⟨w, hw⟩ := span_apply_sum lev hm E (fun p q => blk (stdBlocks d h) p < blk (stdBlocks d h) q)
    (fun p q hpq => by rw [hlevb p, hlevb q]; exact hpq) hc x
  exact ⟨w, by rw [← hw, LinearMap.sub_apply]⟩

end GlobalTheory.CompanionTheory.RgCOBlock

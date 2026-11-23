import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LetterConjugation

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.Proof.exists_descending_letter_chain

theorem down_prefix {T : Type} {m : T → ℕ} {n : ℕ} {u : Fin n → Let m} (hi : Function.Injective u)
    (h : ∀ (l : Fin n) (j : Fin (m (u l).1)), j < (u l).2 → ∃ l' ≤ l, u l' = ⟨(u l).1, j⟩) {k : ℕ} (hk : k ≤ n) :
    Down (u ∘ Fin.castLE hk) := by
  refine ⟨hi.comp (Fin.castLE_injective hk), fun l j hj => ?_⟩
  obtain ⟨l', hl, e⟩ := h (Fin.castLE hk l) j hj
  exact ⟨⟨l'.1, lt_of_le_of_lt (Fin.le_def.1 hl) l.2⟩, e⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem pairwise_letters : (letters Dw).Pairwise fun a b => a.1 = b.1 → (a.2 : ℕ) ≤ (b.2 : ℕ) := by
  refine List.pairwise_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ (List.pairwise_le_finRange _)
    exact fun h _ => Fin.le_def.1 h
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab x hx y hy h => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hy
    exact absurd ((Fintype.equivFin (E →+* ℂ)).symm.injective h) hab

theorem earlier (l : Fin (letters Dw).length) (j : Fin (Dw.mult ((letters Dw).get l).1))
    (hj : j < ((letters Dw).get l).2) : ∃ l' ≤ l, (letters Dw).get l' = ⟨((letters Dw).get l).1, j⟩ := by
  obtain ⟨l', e⟩ := List.get_of_mem (GlobalTheory.Proof.LetterConjugation.mem_letters Dw ⟨((letters Dw).get l).1, j⟩)
  refine ⟨l', not_lt.1 fun hl => ?_, e⟩
  have h := List.pairwise_iff_get.1 (pairwise_letters Dw) l l' hl
  rw [e] at h
  exact absurd (h rfl) (not_le.2 hj)

theorem step_position : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (x : Letter Dw), letterOf Dw st = some x → ∃ (n : ℕ) (u : Fin n → Let Dw.mult) (k : Fin n), Down u ∧ Down (u ∘ Fin.castLE k.2.le) ∧ Down (u ∘ Fin.castLE (Nat.succ_le_of_lt k.2)) ∧ u k = x ∧ ∀ (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (y : Sp C ⟶ X) (fr : Vecs Dw t C) (p : ℕ), lnStep t y fr p false st = Real.log (grNorm t y (latDR t y) (fun i => fr (u i).1 (u i).2) k) := by
  intro E _ _ _ H Dw st x hx
  rcases st with ⟨τ, k⟩ | k
  · by_cases h : k < Dw.mult τ
    · simp only [letterOf, dif_pos h, Option.some.injEq] at hx
      have hi : Function.Injective fun i : Fin (Dw.mult τ) => (⟨τ, i⟩ : Let Dw.mult) :=
        fun i i' h => eq_of_heq (Sigma.mk.inj h).2
      have hd : ∀ (l : Fin (Dw.mult τ)) (j : Fin (Dw.mult τ)), j < l →
          ∃ l' ≤ l, (⟨τ, l'⟩ : Let Dw.mult) = ⟨τ, j⟩ := fun l j hj => ⟨j, hj.le, rfl⟩
      refine ⟨Dw.mult τ, fun i => ⟨τ, i⟩, ⟨k, h⟩, down_prefix hi hd le_rfl, down_prefix hi hd _, down_prefix hi hd _, hx,
        fun X t C _ _ y fr p => ?_⟩
      simp [lnStep, h, lat]
    · simp [letterOf, h] at hx
  · obtain ⟨h, hx⟩ := List.getElem?_eq_some_iff.1 (show (letters Dw)[k]? = some x from hx)
    have hi : Function.Injective (letters Dw).get := List.nodup_iff_injective_get.1 (GlobalTheory.Proof.LetterConjugation.nodup_letters Dw)
    refine ⟨_, (letters Dw).get, ⟨k, h⟩, down_prefix hi (earlier Dw) le_rfl, down_prefix hi (earlier Dw) _,
      down_prefix hi (earlier Dw) _, hx, fun X t C _ _ y fr p => ?_⟩
    simp only [lnStep, dif_pos h, lat]

end GlobalTheory.Proof.exists_descending_letter_chain

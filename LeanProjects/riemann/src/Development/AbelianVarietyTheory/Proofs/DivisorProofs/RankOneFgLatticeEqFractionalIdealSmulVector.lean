import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
open NumberField

namespace GlobalTheory

theorem latRank_one_eq_ideal_smul {K : Type} [Field K] [NumberField K] {m : ℕ}
    (ell : Submodule (𝓞 K) (Fin m → K)) :
    ReciprocityTheory.GeometryOfNumbersTheory.latRank K ell = 1 → ell.FG →
    ∃ v : Fin m → K, v ≠ 0 ∧ ∃ 𝔟 : Submodule (𝓞 K) K, 𝔟.FG ∧ 𝔟 ≠ ⊥ ∧
      ∀ e, e ∈ ell ↔ ∃ β ∈ 𝔟, e = β • v := by
  intro hr hfg
  unfold ReciprocityTheory.GeometryOfNumbersTheory.latRank at hr
  obtain ⟨w, hw0, hw⟩ := (finrank_eq_one_iff').mp hr
  have hvW : (w : Fin m → K) ≠ 0 := by
    intro h; exact hw0 (Subtype.ext h)
  have hmul : ∀ e ∈ ell, ∃ β : K, e = β • (w : Fin m → K) := by
    intro e he
    obtain ⟨c, hc⟩ := hw ⟨e, Submodule.subset_span he⟩
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    exact this.symm
  let f : K →ₗ[𝓞 K] (Fin m → K) :=
    { toFun := fun β => β • (w : Fin m → K)
      map_add' := fun a b => add_smul a b _
      map_smul' := fun r b => by
        simp only [RingHom.id_apply]
        exact smul_assoc r b _ }
  have hf : ∀ β, f β = β • (w : Fin m → K) := fun _ => rfl
  have finj : Function.Injective f := by
    intro a b hab
    rw [hf, hf] at hab
    have : (a - b) • (w : Fin m → K) = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hvW
  refine ⟨w, hvW, ell.comap f, ?_, ?_, ?_⟩
  · apply Submodule.fg_of_fg_map_injective f finj
    have : (ell.comap f).map f = ell := by
      apply le_antisymm (Submodule.map_comap_le _ _)
      intro e he
      obtain ⟨β, rfl⟩ := hmul e he
      exact ⟨β, he, rfl⟩
    rw [this]; exact hfg
  · intro hbot
    apply hw0
    have hell : ell = ⊥ := by
      rw [eq_bot_iff]; intro e he
      obtain ⟨β, rfl⟩ := hmul e he
      have : β ∈ ell.comap f := he
      rw [hbot, Submodule.mem_bot] at this
      simp [this]
    have hW : Submodule.span K (ell : Set (Fin m → K)) = ⊥ := by simp [hell]
    have h0 : ∀ x ∈ Submodule.span K (ell : Set (Fin m → K)), x = 0 := by
      rw [hW]; intro x hx; exact (Submodule.mem_bot K).mp hx
    exact Subtype.ext (h0 _ w.2)
  · intro e
    constructor
    · intro he
      obtain ⟨β, rfl⟩ := hmul e he
      exact ⟨β, he, rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      exact hβ

end GlobalTheory

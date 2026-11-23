import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter

noncomputable section

universe u

namespace RenameIntNum

variable {K₁ K₂ : Type*} (e : K₁ ≃ K₂)

def precompIso : (K₂ → ℤ) ≃o (K₁ → ℤ) where
  toFun m := m ∘ e
  invFun m := m ∘ e.symm
  left_inv m := by funext k; simp
  right_inv m := by funext k; simp
  map_rel_iff' := by
    intro a b
    constructor
    · intro h k
      simpa using h (e.symm k)
    · intro h k
      exact h (e k)

theorem eventualValue_comp (g : (K₁ → ℤ) → ℤ) :
    eventualValue (fun m : K₂ → ℤ => g (m ∘ e)) = eventualValue g := by
  have key : ∀ c, (∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c) ↔
      ∀ᶠ m in atTop, g m = c := by
    intro c
    rw [← (precompIso e).map_atTop, Filter.eventually_map]
    rfl
  unfold eventualValue
  by_cases hg : ∃ c, ∀ᶠ m in atTop, g m = c
  · have hf : ∃ c, ∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c :=
      hg.imp fun c hc => (key c).2 hc
    rw [dif_pos hf, dif_pos hg]
    obtain ⟨m, h1, h2⟩ := (((key _).1 hf.choose_spec).and hg.choose_spec).exists
    exact h1.symm.trans h2
  · have hf : ¬ ∃ c, ∀ᶠ m in atTop, (fun m : K₂ → ℤ => g (m ∘ e)) m = c :=
      fun ⟨c, hc⟩ => hg ⟨c, (key c).1 hc⟩
    rw [dif_neg hf, dif_neg hg]

theorem mixedDiff_comp {n : ℕ} (bs : Fin n → K₂ → ℤ) (h : (K₁ → ℤ) → ℤ) :
    mixedDiff bs (fun m => h (m ∘ e)) = fun m => mixedDiff (fun i => bs i ∘ e) h (m ∘ e) := by
  unfold mixedDiff
  have hl : List.ofFn (fun i => bs i ∘ e) = (List.ofFn bs).map (fun b => b ∘ e) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  generalize List.ofFn bs = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, ih]
    rfl

theorem proof (h : RenameHilbFn.Statement.{u}) : RenameIntNum.Statement.{u} := by
  intro F _ S K' _ _ κ ι' E σ hσ P n bs
  have hH : hilbFn (P.comap (rename σ)) = fun m => hilbFn P (m ∘ E.symm) :=
    funext fun m => h F S K' κ ι' E σ hσ P m
  unfold intNum
  rw [hH, mixedDiff_comp E.symm bs (hilbFn P),
    eventualValue_comp E.symm (mixedDiff (fun i => bs i ∘ E.symm) (hilbFn P))]

end RenameIntNum

end

end GroundTheory.Heights₂.Heights.FieldNumbers

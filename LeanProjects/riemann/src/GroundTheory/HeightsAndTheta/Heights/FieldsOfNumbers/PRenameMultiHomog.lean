import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsRename
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def extendAddHom {K K' : Type} (j : K ↪ K') : (K → ℕ) →+ (K' → ℕ) where
  toFun x := Function.extend j x 0
  map_zero' := by
    funext k'
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      simp [j.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  map_add' x y := by
    funext k'
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      simp [j.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]

theorem weight_mapDomain_blockWeight {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι : K → Type) (ι' : K' → Type) (g : (Σ k, ι k) → (Σ k', ι' k'))
    (hg : ∀ v, (g v).1 = j v.1) (u : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g u) =
      Function.extend j (Finsupp.weight (blockWeight ι) u) 0 := by
  have key : (Finsupp.weight (R := ℕ) (blockWeight ι')).comp
        (Finsupp.mapDomain.addMonoidHom (M := ℕ) g) =
      (extendAddHom j).comp (Finsupp.weight (R := ℕ) (blockWeight ι)) := by
    ext v
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.singleAddHom_apply,
      Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, Finsupp.weight_single,
      one_smul]
    show blockWeight ι' (g v) _ = Function.extend j (blockWeight ι v) 0 _
    rename_i k'
    simp only [blockWeight, hg v]
    by_cases h : ∃ a, j a = k'
    · obtain ⟨a, rfl⟩ := h
      rw [j.injective.extend_apply]
      by_cases hav : a = v.1
      · subst hav; simp
      · rw [Pi.single_eq_of_ne (fun e => hav (j.injective e)), Pi.single_eq_of_ne hav]
    · rw [Function.extend_apply' _ _ _ h, Pi.single_eq_of_ne (fun e => h ⟨v.1, e.symm⟩)]
      rfl
  exact DFunLike.congr_fun key u

theorem RenameMultiHomog.proof : RenameMultiHomog.Statement.{u} := by
  intro R _ K K' _ _ j ι ι' g hg f d hf e he
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero g f e he
  rw [weight_mapDomain_blockWeight j ι ι' g hg u, hf hu]

end

end GroundTheory.Heights₂.Heights.FieldNumbers

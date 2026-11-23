import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.IrreducibleSpan

open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

local notation "𝕢₁" => Function.Periodic.qParam 1

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem weight_pos_of_coeff_one (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) : 0 < k := by
  by_contra hk
  have hk' : k ≤ 0 := not_lt.1 hk
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ τ : ℍ, f τ = c := by
    rcases lt_or_eq_of_le hk' with hlt | rfl
    · have h0 := ModularForm.isZero_of_neg_weight hlt (CuspForm.toModularFormₗ f)
      exact ⟨0, fun τ => congrArg (fun F : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k => F τ) h0⟩
    · obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero (CuspForm.toModularFormₗ f)
      exact ⟨c, fun τ => congrFun hc τ⟩
  have h1 := qExpansion_coeff_eq_of_hasSum f (b := fun n => if n = 0 then c else 0) (fun τ => by
    rw [hc τ]
    convert hasSum_ite_eq 0 c using 2 with n
    split_ifs with h
    · subst h; simp
    · simp) 1
  rw [hf1] at h1
  simp at h1

theorem liftCusp_ne_zero (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) : liftCusp f ≠ 0 := by
  intro h
  have h1 : liftEquiv N k f.toSlashInvariantForm = 0 := by
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have h2 : f.toSlashInvariantForm = 0 := (liftEquiv N k).map_eq_zero_iff.1 h1
  have h3 : f = 0 := by
    ext τ
    exact congrArg (fun F : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k => F τ) h2
  rw [h3] at hf1
  have h4 := qExpansion_coeff_eq_of_hasSum (0 : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (b := fun _ => 0) (fun τ => by simp) 1
  rw [hf1] at h4
  exact one_ne_zero h4

theorem gkfSpan_liftCusp_irreducible (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : ∀ (p : ℕ) [Fact p.Prime], ∃ c : ℂ, heckeCusp N p k f = c • f)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) :
    gkfSpan (liftCusp f) ≠ ⊥ ∧ ∀ W : Submodule ℂ (cuspForms ℚ 2), IsGKFStable W →
      W ≤ gkfSpan (liftCusp f) → W = ⊥ ∨ W = gkfSpan (liftCusp f) := by
  classical
  let ev : ℕ → ℂ := fun p => if h : p.Prime then (haveI : Fact p.Prime := ⟨h⟩; Classical.choose (hf p)) else 0
  have hev : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k f = ev p • f := by
    intro p hp
    have h := Classical.choose_spec (@hf p ⟨hp.out⟩)
    simp only [ev, dif_pos hp.out]
    exact h
  have hk := weight_pos_of_coeff_one f hf1
  refine ⟨fun h => liftCusp_ne_zero f hf1 ?_, fun W hW hWle => ?_⟩
  · have := mem_gkfSpan_self (liftCusp f)
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    · right
      obtain ⟨t, htT, ht0, htW⟩ :=
        exists_ne_zero_mem_translateSpanCusp f hk hW (hWle.trans (gkfSpan_le_weightSpan f)) hW0
      have hY : liftCusp f ∈ W ⊓ translateSpanCusp f :=
        liftCusp_mem_of_le_translateSpanCusp f ev hev hf1 (W ⊓ translateSpanCusp f) inf_le_right
          (fun g y hy => ⟨hW.2.2 g y hy.1, finRepCusp_mem_translateSpanCusp f g hy.2⟩)
          (fun h => ht0 ((Submodule.mem_bot ℂ).1 (h ▸ ⟨htW, htT⟩)))
      exact le_antisymm hWle (gkfSpan_le hW hY.1)

end GL2Classical

end

end GroundTheory.Automorphic

import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic

namespace Formalism.L2.SG.GGMirabolic.Inhab

open Formalism.L2.SG.GGMirabolic

noncomputable section

open Classical

def psi3 : AddChar (ZMod 3) ℂ := ZMod.stdAddChar

theorem additive_char_one_ne_one : psi3 1 ≠ 1 := by
  intro h
  have hn : ∀ n : ℕ, psi3 (n : ZMod 3) = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, AddChar.map_add_eq_mul, ih, h, one_mul]
  have hall : ∀ a : ZMod 3, psi3 a = 1 := by
    intro a
    have := hn a.val
    rwa [ZMod.natCast_zmod_val] at this
  have hprim := ZMod.isPrimitive_stdAddChar 3
  apply hprim (a := 1) one_ne_zero
  rw [AddChar.mulShift_one]
  ext a
  exact hall a

theorem additive_char_nontrivial : psi3 ≠ 1 := by
  intro h; apply additive_char_one_ne_one; rw [h]; rfl

theorem card_zmod3 : 3 ≤ Fintype.card (ZMod 3) := by simp

theorem trivial_isIrreducible (G : Type) [Group G] :
    (Representation.trivial ℂ G ℂ).IsIrreducible := by
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun h => ?_⟩⟩, eq_bot_or_eq_top := fun W => ?_ }
  · have h2 := congrArg (fun W : Subrepresentation (Representation.trivial ℂ G ℂ) => W.toSubmodule) h
    exact (bot_ne_top : (⊥ : Submodule ℂ ℂ) ≠ ⊤) h2
  · rcases IsSimpleOrder.eq_bot_or_eq_top W.toSubmodule with h | h
    · left; apply Subrepresentation.toSubmodule_injective; rw [h]; rfl
    · right; apply Subrepresentation.toSubmodule_injective; rw [h]; rfl

theorem superdiagonal_gl1_eq_zero (x : Matrix (Fin 1) (Fin 1) (ZMod 3)) : superdiag 1 x = 0 := by
  simp [superdiag]

theorem trivial_gl1_generic : Generic psi3 (Representation.trivial ℂ (GL (Fin 1) (ZMod 3)) ℂ) := by
  refine ⟨LinearMap.id, fun h => ?_, fun u _ v => ?_⟩
  · have := LinearMap.congr_fun h 1; simp at this
  · simp [psiU, superdiagonal_gl1_eq_zero]

def u12 : GL (Fin 2) (ZMod 3) :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem elementary_unipotent_is_unipotent : IsUni 2 u12 := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> simp [u12]
  · fin_cases i <;> fin_cases j <;> simp_all [u12]

theorem character_elementary_unipotent : psiU psi3 u12 = psi3 1 := by
  simp [psiU, superdiag, u12, Fin.sum_univ_two]

theorem trivial_gl2_not_generic : ¬ Generic psi3 (Representation.trivial ℂ (GL (Fin 2) (ZMod 3)) ℂ) := by
  rintro ⟨ℓ, hℓ, hw⟩
  apply hℓ
  refine LinearMap.ext fun v => ?_
  have h := hw u12 elementary_unipotent_is_unipotent v
  rw [character_elementary_unipotent, Representation.trivial_apply] at h
  have h2 : (1 - psi3 1) * ℓ v = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3).symm additive_char_one_ne_one
  · simpa using h3

theorem mirabolic_bound_gl2_f3 : ∏ i ∈ Finset.Ico 1 2, (Fintype.card (ZMod 3) ^ i - 1) = 2 ∧
    Module.finrank ℂ ℂ = 1 := by
  refine ⟨?_, Module.finrank_self ℂ⟩
  simp

theorem regular_free {G : Type} [Group G] (x : Gᵐᵒᵖ) (j : G) (h : x • j = j) : x = 1 := by
  rw [MulOpposite.smul_eq_mul_unop] at h
  have : MulOpposite.unop x = 1 := by simpa using h
  simpa using congrArg MulOpposite.op this

theorem regular_quot {G : Type} [Group G] (i j : G) : MulOpposite.op (j⁻¹ * i) • j = i := by
  rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_inv_cancel_left]

theorem cardU_pos (F : Type) [Field F] [Fintype F] (k : ℕ) : 0 < cardU F k := by
  unfold cardU
  have : Nonempty {x : GL (Fin k) F // IsUni k x} := ⟨⟨1, isUni_one⟩⟩
  exact Nat.card_pos

theorem gam_one_ne_zero (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) :
    gam ψ₀ (1 : GL (Fin k) F) ≠ 0 := by
  rw [gam_one]
  have h1 : (Fintype.card (GL (Fin k) F) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 : (cardU F k : ℂ) ≠ 0 := by exact_mod_cast (cardU_pos F k).ne'
  exact div_ne_zero h1 h2

end

end Formalism.L2.SG.GGMirabolic.Inhab

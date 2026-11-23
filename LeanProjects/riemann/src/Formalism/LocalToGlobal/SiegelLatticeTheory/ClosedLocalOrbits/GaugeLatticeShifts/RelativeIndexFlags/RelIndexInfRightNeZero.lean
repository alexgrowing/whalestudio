import Mathlib

noncomputable section

namespace Formalism.L2.SG.Pf.RelativeIndexFlags

variable {G : Type*} [Group G]

def ratio (A S : Subgroup G) : ℝ := (A.relIndex S : ℝ) / (S.relIndex A : ℝ)

theorem real_ratio_eq (a e c f β δ : ℕ) (hβ : β ≠ 0) (hδ : δ ≠ 0) (h1 : β * a = δ * c)
    (h2 : β * e = δ * f) : (a : ℝ) / e = c / f := by
  have hβ' : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
  have hδ' : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ
  have h1' : (β : ℝ) * a = δ * c := by exact_mod_cast h1
  have h2' : (β : ℝ) * e = δ * f := by exact_mod_cast h2
  rw [← mul_div_mul_left (a : ℝ) (e : ℝ) hβ', h1', h2', mul_div_mul_left _ _ hδ']

theorem relIndex_inf_right_ne_zero {T S : Subgroup G} (h : T.relIndex S ≠ 0) (B : Subgroup G) :
    T.relIndex (S ⊓ B) ≠ 0 := by
  have h1 := Subgroup.relIndex_inter_ne_zero h B
  rw [← Subgroup.inf_relIndex_right] at h1 ⊢
  have e : T ⊓ B ⊓ (S ⊓ B) = T ⊓ (S ⊓ B) := by
    ext x; simp only [Subgroup.mem_inf]; tauto
  rwa [e] at h1

theorem ratio_eq_of_comm (S T B : Subgroup G) (hk : T.relIndex S = S.relIndex T)
    (hk0 : T.relIndex S ≠ 0) : ratio B S = ratio B T := by
  have hk0' : S.relIndex T ≠ 0 := hk ▸ hk0
  have hβ : T.relIndex (S ⊓ B) ≠ 0 := relIndex_inf_right_ne_zero hk0 B
  have hδ : S.relIndex (T ⊓ B) ≠ 0 := relIndex_inf_right_ne_zero hk0' B

  have e1 := Subgroup.relIndex_inf_mul_relIndex B T S
  have e2 := Subgroup.relIndex_inf_mul_relIndex B S T
  have eP : (B ⊓ T).relIndex S = (B ⊓ S).relIndex T := by
    rw [← e1, ← e2, inf_comm T S, hk]
  have e3 := Subgroup.relIndex_inf_mul_relIndex T B S
  have e4 := Subgroup.relIndex_inf_mul_relIndex S B T
  have e5 := Subgroup.relIndex_inf_mul_relIndex T S B
  have e6 := Subgroup.relIndex_inf_mul_relIndex S T B
  unfold ratio
  refine real_ratio_eq _ _ _ _ (T.relIndex (S ⊓ B)) (S.relIndex (T ⊓ B)) hβ hδ ?_ ?_
  · rw [inf_comm S B, inf_comm T B, e3, e4, inf_comm T B, inf_comm S B, eP]
  · rw [e5, e6, inf_comm]

theorem ratio_map_equiv (φ : G ≃* G) (A S : Subgroup G) :
    ratio (A.map φ.toMonoidHom) (S.map φ.toMonoidHom) = ratio A S := by
  unfold ratio
  rw [Subgroup.relIndex_map_map_of_injective _ _ φ.injective,
    Subgroup.relIndex_map_map_of_injective _ _ φ.injective]

abbrev cj (g : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

theorem ratio_cj_of (A S : Subgroup G) (g : G)
    (hA1 : A.relIndex S ≠ 0) (hA2 : S.relIndex A ≠ 0)
    (hB1 : (cj g A).relIndex S ≠ 0) (hB2 : S.relIndex (cj g A) ≠ 0)
    (hU : S.relIndex (cj g S) ≠ 0 → (cj g S).relIndex S ≠ 0 →
      S.relIndex (cj g S) = (cj g S).relIndex S) :
    ratio (cj g A) S = ratio A S := by
  have m1 : (cj g S).relIndex (cj g A) ≠ 0 := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]; exact hA2
  have m2 : (cj g A).relIndex (cj g S) ≠ 0 := by
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]; exact hA1
  have hTS : (cj g S).relIndex S ≠ 0 := Subgroup.relIndex_ne_zero_trans m1 hB1
  have hST : S.relIndex (cj g S) ≠ 0 := Subgroup.relIndex_ne_zero_trans hB2 m2
  have hk := (hU hST hTS).symm
  rw [ratio_eq_of_comm S (cj g S) (cj g A) hk hTS]
  exact ratio_map_equiv (MulAut.conj g) A S

end Formalism.L2.SG.Pf.RelativeIndexFlags

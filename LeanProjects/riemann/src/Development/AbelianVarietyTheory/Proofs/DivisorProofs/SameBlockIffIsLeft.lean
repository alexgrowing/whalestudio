import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem eab_mul_eab {p q : ℕ} (a b c d : Ix p q) :
    Eab a b * Eab c d = if b = c then Eab a d else 0 := by
  unfold Eab
  split_ifs with h
  · subst h; rw [Matrix.single_mul_single_same, mul_one]
  · exact Matrix.single_mul_single_of_ne _ _ _ _ h _

theorem mat_eq_sum_eab {p q : ℕ} (X : Mat p q) : X = ∑ a, ∑ b, X a b • Eab a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  unfold Eab; rw [Matrix.smul_single, smul_eq_mul, mul_one]

theorem act_eq_sum_units {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (X : Mat p q) (v : V) :
    act X v = ∑ a, ∑ b, X a b • units act a b v := by
  conv_lhs => rw [mat_eq_sum_eab X]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, units]

theorem sameBlock_iff_isLeft {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp [sameBlock]

theorem lie_units_stab : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V),
    (IsLieAct act → IsGl (units act)) ∧
    (∀ N : Submodule ℂ V, (∀ a b : Ix p q, a.isLeft = b.isLeft → ∀ u ∈ N, units act a b u ∈ N) ↔ KStable act N) ∧
    ∀ N : Submodule ℂ V, (∀ a b, ∀ u ∈ N, units act a b u ∈ N) → Stab act N := by
  intro p q V _ _ act
  refine ⟨fun hL a b c d => ?_, fun N => ⟨fun h X hX w hw => ?_, fun h a b hab u hu => ?_⟩, fun N h Z y hy => ?_⟩
  · simp only [units]
    rw [← hL, eab_mul_eab, eab_mul_eab, map_sub]
    congr 1
    · split_ifs <;> simp
    · split_ifs <;> simp
  · rw [act_eq_sum_units]
    refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
    by_cases hab : a.isLeft = b.isLeft
    · exact N.smul_mem _ (h a b hab w hw)
    · rw [hX a b (fun hs => hab ((sameBlock_iff_isLeft a b).1 hs)), zero_smul]; exact N.zero_mem
  · refine h (Eab a b) (fun c d hcd => ?_) u hu
    unfold Eab
    rw [Matrix.single_apply]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'; exact absurd ((sameBlock_iff_isLeft _ _).2 hab) hcd
    · rfl
  · rw [act_eq_sum_units]
    exact N.sum_mem fun a _ => N.sum_mem fun b _ => N.smul_mem _ (h a b y hy)

end GlobalTheory.HoweR

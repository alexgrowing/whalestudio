import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet.ModRel

theorem ew_append {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V)
    (l₁ l₂ : List (Fin n × Fin n)) : ew E (l₁ ++ l₂) = ew E l₁ * ew E l₂ := by
  induction l₁ with
  | nil => simp [ew]
  | cons p w ih => simp only [List.cons_append, ew, ih, mul_assoc]

theorem thetaA_one_onePositionArrayOfIsometry {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (G : Fin n × Fin n → W) : thetaA E 1 (arr1 j G) = ∑ p : Fin n × Fin n, E p.1 p.2 (j (G p)) := by
  rw [theta_map_word_sum_apply]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun α => ?_
  simp [ew, arr1, arrTo]

theorem theta_vminus {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V} (hg : GlRel E)
    (h0 : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) :
    Vminus ε E Λ u ≤ LinearMap.ker (thetaA E 1) := by
  obtain ⟨-, hθ⟩ := (arrModule V n ε E 1).1 hg
  apply isotypic_part_le_of_forall
  intro y hy μ hμ hyh
  apply compact_span_le_of_stable
  · intro c d _ x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hθ, hx, map_zero]
  · rw [LinearMap.mem_ker]
    obtain ⟨a, b, hba, hne, rfl⟩ := hμ
    have hμeq : Λ + root a b = Λ - root b a := by
      rw [root_swap' a b, sub_eq_add_neg]
    refine h0 b a hba (Ne.symm hne) _ ⟨fun c => ?_, fun c d hcd hcomp => ?_⟩
    · rw [← hθ, hyh.1 c, map_smul, hμeq]
    · rw [← hθ, hyh.2 c d hcd hcomp, map_zero]

theorem modJet_jetRel (V W : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ)
    (u : V) (j : W →ₗᵢ[ℂ] V) (hL : LowData ε E Λ u j)
    (h0 : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ x : V, KHighest ε E (Λ - root a b) x → x = 0) :
    JetRel ε E Λ u j (modJet E j) := by
  obtain ⟨hg, hu, -, -, -⟩ := hL
  refine ⟨fun l₁ l₂ a b c d => ?_, fun l a b _ y x x' hx => ?_, fun l a b hab y y' x hy => ?_,
    fun l G hG y => ?_⟩
  · have key : ew E (l₁ ++ (a, b) :: (c, d) :: l₂) - ew E (l₁ ++ (c, d) :: (a, b) :: l₂) =
        (if b = c then ew E (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then ew E (l₁ ++ (c, b) :: l₂) else 0) := by
      have h := hg a b c d
      simp only [ew_append, ew]
      rw [← mul_sub, ← mul_assoc (E a b), ← mul_assoc (E c d), ← sub_mul, h]
      split_ifs <;> simp [mul_sub, sub_mul]
    ext y x
    have h2 := congrArg (fun T : Module.End ℂ V => ⟪j y, T (j x)⟫_ℂ) key
    split_ifs at h2 ⊢ <;>
      simpa [modJet_apply, inner_sub_right] using h2
  · simp only [modJet_apply, ew_append, ew, hx, mul_one, Module.End.mul_apply]
  · simp only [modJet_apply, ew, hy, Module.End.mul_apply]
    rw [isUnitary_kUnit ε E hu b a hab.symm]
  · have h := theta_vminus hg h0 hG
    rw [LinearMap.mem_ker, thetaA_one_onePositionArrayOfIsometry] at h
    simp only [modJet_apply, ew_append, ew, mul_one, Module.End.mul_apply]
    rw [← inner_sum, ← map_sum, h, map_zero, inner_zero_right]

end GlobalTheory.SphJet.ModRel

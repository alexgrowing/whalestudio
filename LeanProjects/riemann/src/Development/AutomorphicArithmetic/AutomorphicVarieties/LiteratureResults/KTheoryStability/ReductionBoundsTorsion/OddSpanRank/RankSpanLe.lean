import Mathlib

open scoped TensorProduct

namespace PositivityTheory.KB.TwOdd

theorem rank_span_le {A : Type} [AddCommGroup A] [inst : Module ℤ A] (S : Set A) {ι C : Type} [Fintype ι] [AddCommGroup C]
    [Module ℝ C] (θ : C →ₗ[ℝ] ℝ ⊗[ℤ] A) (T : C →ₗ[ℝ] (ι → ℝ)) (h0 : ∀ z, T z = 0 → θ z = 0)
    (hS : ∀ s ∈ S, ∃ z, θ z = (1 : ℝ) ⊗ₜ s) :
    Module.rank ℤ (Submodule.span ℤ S) ≤ Fintype.card ι := by
  classical
  obtain rfl : inst = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  have hker : LinearMap.ker T ≤ LinearMap.ker θ := fun z hz => h0 z hz
  have hrank : Module.rank ℝ (LinearMap.range θ) ≤ Fintype.card ι := by
    have e1 : LinearMap.range ((LinearMap.ker T).liftQ θ hker) = LinearMap.range θ :=
      Submodule.range_liftQ _ _ _
    calc Module.rank ℝ (LinearMap.range θ)
        = Module.rank ℝ (LinearMap.range ((LinearMap.ker T).liftQ θ hker)) := by rw [e1]
      _ ≤ Module.rank ℝ (C ⧸ LinearMap.ker T) := rank_range_le _
      _ = Module.rank ℝ (LinearMap.range T) := T.quotKerEquivRange.rank_eq
      _ ≤ Module.rank ℝ (ι → ℝ) := Submodule.rank_le _
      _ = Fintype.card ι := by simp
  have hmem : ∀ x ∈ Submodule.span ℤ S, (1 : ℝ) ⊗ₜ[ℤ] x ∈ LinearMap.range θ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨z, hz⟩ := hS s hs
      exact ⟨z, hz⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [TensorProduct.tmul_add]
      exact add_mem hx hy
    | smul n x _ hx =>
      rw [TensorProduct.tmul_smul]
      exact zsmul_mem hx n
  apply rank_le
  intro s hs
  have hA : LinearIndependent ℤ (fun i : s => ((i : Submodule.span ℤ S) : A)) :=
    hs.map' (Submodule.span ℤ S).subtype (Submodule.ker_subtype _)
  have hR := Module.Flat.linearIndependent_one_tmul (S := ℝ) hA
  let w : s → LinearMap.range θ := fun i =>
    ⟨(1 : ℝ) ⊗ₜ[ℤ] ((i : Submodule.span ℤ S) : A), hmem _ (i : Submodule.span ℤ S).2⟩
  have hw : LinearIndependent ℝ w := LinearIndependent.of_comp (LinearMap.range θ).subtype hR
  have h2 := hw.cardinal_le_rank.trans hrank
  simpa using h2

end PositivityTheory.KB.TwOdd

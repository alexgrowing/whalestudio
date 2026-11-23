import Mathlib

noncomputable def UpperTheory.Reformulated.B.EvaluationMap.coeffSpan :
    {K W : Type} →
      [inst : Group K] →
        [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module ℂ W] → Representation ℂ K W → Submodule ℂ (K → ℂ) :=
    fun {K W : Type} [Group K] [AddCommGroup W] [_root_.Module ℂ W] (ρ : Representation ℂ K W) ↦
      Submodule.span ℂ
        {f : K → ℂ | ∃ (ℓ : Module.Dual ℂ W) (w : W), f = fun (k : K) ↦ (ℓ : W → ℂ) (((ρ : K → W →ₗ[ℂ] W) k : W → W) w)}

namespace UpperTheory.Reformulated.B.EvaluationMap.Helpers

private noncomputable def Φ {K W : Type} [Group K] [AddCommGroup W] [_root_.Module ℂ W]
    (ρ : Representation ℂ K W) : Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (K → ℂ) where
  toFun φ := fun k => φ (ρ k)
  map_add' φ ψ := by funext k; simp
  map_smul' c φ := by funext k; simp

private noncomputable def evw {W : Type} [AddCommGroup W] [_root_.Module ℂ W]
    (ℓ : Module.Dual ℂ W) (w : W) : Module.Dual ℂ (W →ₗ[ℂ] W) where
  toFun A := ℓ (A w)
  map_add' A B := by simp
  map_smul' c A := by simp

end UpperTheory.Reformulated.B.EvaluationMap.Helpers

open UpperTheory.Reformulated.B.EvaluationMap.Helpers in
theorem UpperTheory.Reformulated.B.EvaluationMap.main :
    ∀ {K W : Type} [inst : Group K] [inst_1 : AddCommGroup W] [inst_2 : _root_.Module ℂ W] [FiniteDimensional ℂ W]
      (ρ : Representation ℂ K W), FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ) := by
  intro K W _ _ _ _ ρ
  have hle : UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ ≤ LinearMap.range (Φ ρ) := by
    unfold UpperTheory.Reformulated.B.EvaluationMap.coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨evw ℓ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

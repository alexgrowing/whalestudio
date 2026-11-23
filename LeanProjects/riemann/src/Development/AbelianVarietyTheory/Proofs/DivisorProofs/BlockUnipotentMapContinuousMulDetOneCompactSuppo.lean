import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory

theorem blockUnipotent_props : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N a b : ℕ) (e : Fin N ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → k) → GL (Fin N) k), (∀ X, (u X : Matrix (Fin N) (Fin N) k) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) → Continuous u ∧ (∀ X Y, u (X + Y) = u X * u Y) ∧ (∀ X, (u X : Matrix (Fin N) (Fin N) k).det = 1) ∧ ∀ f : GL (Fin N) k → ℂ, HasCompactSupport f → ∀ g h : GL (Fin N) k, HasCompactSupport (fun X => f (g * (h⁻¹ * u X * h))) := by
  intro k _ _ _ _ N a b e u hu
  have hmul : ∀ X Y, u (X + Y) = u X * u Y := by
    intro X Y
    ext1
    rw [Units.val_mul, hu, hu, hu]
    simp only [Matrix.reindex_apply, Equiv.symm_symm]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    congr 1
    simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.of_add_of]
    rw [add_comm X Y]
  have h0 : u 0 = 1 := by
    have := hmul 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  have hinv : ∀ X, (u X)⁻¹ = u (-X) := by
    intro X
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← hmul, neg_add_cancel, h0]
  have hentry : ∀ X p q, (u X : Matrix (Fin N) (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q)) = X p q := by
    intro X p q
    rw [hu]; simp [Matrix.reindex_apply]
  have hval : Continuous (fun X => (u X : Matrix (Fin N) (Fin N) k)) := by
    have : (fun X => (u X : Matrix (Fin N) (Fin N) k)) = fun X => Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1) := funext hu
    rw [this]
    refine Continuous.matrix_reindex ?_ _ _
    exact Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const
  have hcont : Continuous u := by
    rw [Units.continuous_iff]
    refine ⟨hval, ?_⟩
    simp only [hinv]
    exact hval.comp continuous_neg
  refine ⟨hcont, hmul, ?_, ?_⟩
  · intro X
    rw [hu, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    simp
  · intro f hf g h
    set C : Set (GL (Fin N) k) := (fun y => h * (g⁻¹ * y) * h⁻¹) '' tsupport f with hC
    have hCc : IsCompact C := hf.isCompact.image (by fun_prop)
    let E : Fin a → Fin b → GL (Fin N) k → k := fun p q y => (y : Matrix (Fin N) (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q))
    have hE : ∀ p q, Continuous (E p q) := by
      intro p q
      exact (continuous_apply_apply _ _).comp (Units.continuous_val (M := Matrix (Fin N) (Fin N) k))
    refine HasCompactSupport.intro (K := Set.pi Set.univ (fun p => Set.pi Set.univ (fun q => E p q '' C))) ?_ ?_
    · exact isCompact_univ_pi (fun p => isCompact_univ_pi (fun q => hCc.image (hE p q)))
    · intro X hX
      by_contra hne
      apply hX
      have hs : g * (h⁻¹ * u X * h) ∈ tsupport f := subset_tsupport _ hne
      have huC : u X ∈ C := ⟨_, hs, by simp [mul_assoc]⟩
      intro p _ q _
      exact ⟨u X, huC, hentry X p q⟩

end GlobalTheory

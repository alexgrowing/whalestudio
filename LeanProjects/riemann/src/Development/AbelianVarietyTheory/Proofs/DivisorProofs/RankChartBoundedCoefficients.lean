import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorBoxEqCharSum
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankChart

open ValuativeRel

def coeffOnChart {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] (τ : R → D)
    (Y : Matrix (R ⊕ T) D k) : Matrix T R k :=
  (Y.submatrix Sum.inl τ).det⁻¹ • (Y.toRows₂.submatrix id τ * (Y.submatrix Sum.inl τ).adjugate)

theorem coeffOnChart_stack {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
    [Fintype D] [DecidableEq D] (τ : R → D)
    (Y₁ : Matrix R D k) (C : Matrix T R k) (h : (Y₁.submatrix id τ).det ≠ 0) :
    coeffOnChart τ (stack Y₁ C) = C := by
  have e1 : (stack Y₁ C).submatrix Sum.inl τ = Y₁.submatrix id τ := by
    rw [submatrix_inl_eq, toRows₁_stack]
  have e2 : (stack Y₁ C).toRows₂.submatrix id τ = C * Y₁.submatrix id τ := by
    ext i j; simp [stack, Matrix.mul_apply]
  rw [coeffOnChart, e1, e2, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ h, one_smul]

theorem coeffOnChart_continuousOn {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [ContinuousInv₀ k] {R T D : Type} [Fintype R] [DecidableEq R] (τ : R → D) :
    ContinuousOn (coeffOnChart (T := T) (k := k) τ) {Y | (Y.submatrix Sum.inl τ).det ≠ 0} := by
  have hA : Continuous fun Y : Matrix (R ⊕ T) D k => Y.submatrix Sum.inl τ :=
    continuous_id.matrix_submatrix _ _
  have hB : Continuous fun Y : Matrix (R ⊕ T) D k => Y.toRows₂.submatrix id τ :=
    (continuous_id.matrix_submatrix Sum.inr id).matrix_submatrix _ _
  exact ContinuousOn.smul (f := fun Y : Matrix (R ⊕ T) D k => (Y.submatrix Sum.inl τ).det⁻¹)
    (hA.matrix_det.continuousOn.inv₀ fun Y hY => hY) (hB.matrix_mul hA.matrix_adjugate).continuousOn

theorem bounded_coeff_of_SB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] (τ : R → D) :
    ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) →
      ∃ a : kˣ, ∀ (Y₁ : Matrix R D k) (C : Matrix T R k), f (GlobalTheory.RankChart.stack Y₁ C) ≠ 0 →
        C ∈ GlobalTheory.LocMod.Inhab.box T R a := by
  intro f hf hdet
  have hcl : IsClosed (Function.support f) := by
    have := (hf.1.isOpen_fiber 0).isClosed_compl
    simpa [Function.support, Set.compl_setOf] using this
  have hK : IsCompact (Function.support f) := by
    have h2 : HasCompactSupport f := hf.2
    rw [HasCompactSupport, tsupport, hcl.closure_eq] at h2
    exact h2
  have hcont : ContinuousOn (coeffOnChart (T := T) (k := k) τ) (Function.support f) :=
    (coeffOnChart_continuousOn τ).mono fun Y hY => hdet Y hY
  obtain ⟨a, ha⟩ := GlobalTheory.BoxCharComb.exists_box_superset (hK.image_of_continuousOn hcont)
  refine ⟨a, fun Y₁ C hY => ?_⟩
  have hd := hdet _ hY
  rw [submatrix_inl_eq, toRows₁_stack] at hd
  have := ha _ ⟨_, hY, coeffOnChart_stack τ Y₁ C hd⟩
  exact this

end GlobalTheory.RankChart
end

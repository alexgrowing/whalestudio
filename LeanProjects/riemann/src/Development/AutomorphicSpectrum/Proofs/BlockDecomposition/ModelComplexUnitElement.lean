import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem lid_lTensor_unit {R A B : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A]
    [Module R B] (f : A →ₗ[R] B) (u : R ⊗[R] A) :
    TensorProduct.lid R B (f.lTensor R u) = f (TensorProduct.lid R A u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul r a => simp

theorem d0_one {R C : Type} [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) :
    d0 F (1 : C0 F) = 0 := by
  funext T T' φ
  simp [d0]

theorem unit_of_model : ∀ (R C P₀ P₁ P₂ : Type) [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂]
    (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F)
    (ψ₂ : P₂ →ₗ[R] C2 F), IsModel F a₀ a₁ ψ₀ ψ₁ ψ₂ → ∃ e : P₀, a₀ e = 0 ∧ ψ₀ e = 1 := by
  intro R C P₀ P₁ P₂ _ _ F _ _ _ _ _ _ a₀ a₁ ψ₀ ψ₁ ψ₂ h
  obtain ⟨-, -, -, hM⟩ := h
  obtain ⟨x, y, h1, h2⟩ := (hM (ModuleCat.of R R)).1.2 ((1 : R) ⊗ₜ[R] (1 : C0 F))
    (by simp [d0_one F])
  have h1' : a₀.lTensor R x = 0 := h1
  have h2' : ψ₀.lTensor R x - (1 : R) ⊗ₜ[R] (1 : C0 F) = 0 := by simpa using h2
  refine ⟨TensorProduct.lid R P₀ x, ?_, ?_⟩
  · rw [← lid_lTensor_unit, h1', map_zero]
  · rw [← lid_lTensor_unit, sub_eq_zero.mp h2']
    simp

end GlobalTheory.CompanionTheory.PerfVB

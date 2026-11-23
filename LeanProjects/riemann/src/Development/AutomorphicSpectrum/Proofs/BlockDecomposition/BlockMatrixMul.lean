import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

def CovAt {D : D7} {n : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {θ : InfFam D}
    (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (γ : G D n) : Prop :=
  ∀ (v : Mx D V.rank (n + n)) (Φ Ψ : schwartzA θ V.rank n), Ψ.1 = Heisenberg₂ ψ V v Φ.1 →
    (ω γ Ψ).1 = Heisenberg₂ ψ V (HMul.hMul v (mat γ⁻¹)) (ω γ Φ).1

def FieldGen (K : Type) [Field K] (σ : K →+* K) (n : ℕ) : Prop :=
  ∀ T : Matrix (Fin (n + n)) (Fin (n + n)) K → Prop, (∀ g h, T g → T h → T (g * h)) →
    (∀ a : Matrix (Fin n) (Fin n) K, IsUnit a.det → T (mA σ a)) →
    (∀ b : Matrix (Fin n) (Fin n) K, cT σ b = b → T (nB b)) → T (Jm K n) →
    ∀ g, IsUnit g.det → IsUnitary σ (Jm K n) g → T g

variable {D : D7} {n : ℕ}

theorem mat_mul' (g h : G D n) : mat (g * h) = mat g * mat h := by
  unfold mat; rw [map_mul]; rfl

theorem mat_one' : mat (1 : G D n) = 1 := by
  unfold mat; rw [map_one]; rfl

theorem mat_inv_mul' (g : G D n) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

theorem mat_mul_inv' (g : G D n) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul', mul_inv_cancel, mat_one']

theorem mat_injective' : Function.Injective (mat : G D n → Mx D (n + n) (n + n)) :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem x_part_mul_block {m : ℕ} (v : Mx D m (n + n)) (A B C E : Mx D n n) :
    xPart (HMul.hMul v (blk4 A B C E) : Mx D m (n + n)) = HMul.hMul (xPart v) A + HMul.hMul (yPart v) C := by
  funext i j
  simp only [xPart, yPart, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]

theorem y_part_mul_block {m : ℕ} (v : Mx D m (n + n)) (A B C E : Mx D n n) :
    yPart (HMul.hMul v (blk4 A B C E) : Mx D m (n + n)) = HMul.hMul (xPart v) B + HMul.hMul (yPart v) E := by
  funext i j
  simp only [xPart, yPart, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂]

theorem submatrix_fromBlocks_mul {R : Type} [CommRing R] (A B C E A' B' C' E' : Matrix (Fin n) (Fin n) R) :
    blk4 A B C E * blk4 A' B' C' E' = blk4 (A * A' + B * C') (A * B' + B * E') (C * A' + E * C') (C * B' + E * E') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem covAt_mul {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {θ : InfFam D}
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {γ₁ γ₂ : G D n}
    (h₁ : CovAt ψ V ω γ₁) (h₂ : CovAt ψ V ω γ₂) : CovAt ψ V ω (γ₁ * γ₂) := by
  intro v Φ Ψ hΨ
  have e1 := h₁ _ (ω γ₂ Φ) (ω γ₂ Ψ) (h₂ v Φ Ψ hΨ)
  rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, mul_inv_rev, mat_mul', Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.EisCovar

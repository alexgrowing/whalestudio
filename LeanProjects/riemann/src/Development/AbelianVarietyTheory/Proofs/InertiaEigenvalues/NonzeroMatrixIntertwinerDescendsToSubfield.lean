import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory

theorem matrix_intertwiner_descends : ∀ (K : Type) [Field K] (e : K →+* ℂ) (Γ m p : Type) [Fintype m] [Fintype p] (A : Γ → Matrix m m K) (B : Γ → Matrix p p K), (∃ X : Matrix p m ℂ, X ≠ 0 ∧ ∀ γ, X * (A γ).map e = (B γ).map e * X) → ∃ X : Matrix p m K, X ≠ 0 ∧ ∀ γ, X * A γ = B γ * X := by
  intro K _ e Γ m p _ _ A B ⟨X, hX, hXc⟩
  letI := e.toAlgebra
  obtain ⟨a, b, hab⟩ : ∃ a b, X a b ≠ 0 := by
    by_contra h
    push_neg at h
    exact hX (Matrix.ext h)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual K ℂ, ℓ (X a b) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hab ((Module.forall_dual_apply_eq_zero_iff K (X a b)).1 h)
  have h1 : ∀ (x : ℂ) (c : K), ℓ (x * e c) = ℓ x * c := by
    intro x c
    have : x * e c = c • x := by rw [Algebra.smul_def, mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have h2 : ∀ (x : ℂ) (c : K), ℓ (e c * x) = c * ℓ x := by
    intro x c
    have : e c * x = c • x := by rw [Algebra.smul_def]; rfl
    rw [this, map_smul, smul_eq_mul]
  refine ⟨X.map ℓ, ?_, fun γ => ?_⟩
  · intro h
    apply hℓ
    have := congrFun (congrFun h a) b
    simpa using this
  · ext i j
    have key := congrArg (fun M => ℓ (M i j)) (hXc γ)
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, h1, h2] at key ⊢
    exact key

end GlobalTheory

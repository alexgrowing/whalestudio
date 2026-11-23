import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe

open MvPolynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm

open Formalism.BasicNotions Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {n n' : ℕ}

def placeNorm (lam : DomWeight n) (f : nablaSq ℂ n lam) : ℝ :=
  Real.sqrt (normFock lam f.1 f.1).re

def coefNorm (lam : ι → DomWeight n) (F : VV ℂ lam) : ℝ :=
  Real.sqrt (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) F F).re

def pureTen (lam : ι → DomWeight n) (f : ∀ τ, nablaSq ℂ n (lam τ)) : VV ℂ lam :=
  ⟨ten fun τ => (f τ).1, Submodule.subset_span ⟨fun τ => (f τ).1, fun τ => (f τ).2, rfl⟩⟩

def IsTensorMap (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') : Prop :=
  ∀ f : ∀ τ, nablaSq ℂ n (lam τ), T (pureTen lam f) = pureTen lam' fun τ => A τ (f τ)

def TensorNormBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (c : ι → ℝ),
    (∀ τ, 0 ≤ c τ) →
    (∀ τ (f : nablaSq ℂ n (lam τ)), placeNorm (lam' τ) (A τ f) ≤ c τ * placeNorm (lam τ) f) →
    (∃! T : VV ℂ lam →ₗ[ℂ] VV ℂ lam', IsTensorMap lam lam' A T) ∧
      ∀ T : VV ℂ lam →ₗ[ℂ] VV ℂ lam', IsTensorMap lam lam' A T →
        ∀ F : VV ℂ lam, coefNorm lam' (T F) ≤ (∏ τ, c τ) * coefNorm lam F

theorem fockF_eq_fockS {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f = fockS f f := by
  unfold Formalism.REAL.fockF fockS mfact
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

theorem fockS_self_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : ∃ r : ℝ, 0 ≤ r ∧ fockS f f = r := by
  refine ⟨∑ m ∈ f.support, ‖f.coeff m‖ ^ 2 * (mfact m : ℝ), by positivity, ?_⟩
  unfold fockS
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Complex.conj_mul']
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.TensorPlaceNorm

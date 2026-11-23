import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod

open MvPolynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds

open Formalism.BasicNotions Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {n n' : ℕ}

def nsqOne (lam : DomWeight n) (f : nablaSq ℂ n lam) : ℝ :=
  (normFock lam (f : MvPolynomial (Fin n × Fin n) ℂ) (f : MvPolynomial (Fin n × Fin n) ℂ)).re

def nsqAll (lam : ι → DomWeight n) (F : VV ℂ lam) : ℝ :=
  (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) F F).re

def NormLeOne {lam : DomWeight n} {lam' : DomWeight n'} (A : nablaSq ℂ n lam →ₗ[ℂ] nablaSq ℂ n' lam') (c : ℝ) :
    Prop :=
  0 ≤ c ∧ ∀ f, nsqOne lam' (A f) ≤ c ^ 2 * nsqOne lam f

def NormLeAll {lam : ι → DomWeight n} {lam' : ι → DomWeight n'} (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (c : ℝ) : Prop :=
  0 ≤ c ∧ ∀ F, nsqAll lam' (T F) ≤ c ^ 2 * nsqAll lam F

def tenV (lam : ι → DomWeight n) (f : ∀ τ, nablaSq ℂ n (lam τ)) : VV ℂ lam :=
  ⟨ten fun τ => (f τ : MvPolynomial (Fin n × Fin n) ℂ),
    Submodule.subset_span ⟨fun τ => (f τ : MvPolynomial (Fin n × Fin n) ℂ), fun τ => (f τ).2, rfl⟩⟩

def IsTensorMap {lam : ι → DomWeight n} {lam' : ι → DomWeight n'}
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') : Prop :=
  ∀ f : ∀ τ, nablaSq ℂ n (lam τ), T (tenV lam f) = tenV lam' fun τ => A τ (f τ)

def TensorNormLe : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)),
    (∃ T : VV ℂ lam →ₗ[ℂ] VV ℂ lam', IsTensorMap A T) ∧
    ∀ (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam'), IsTensorMap A T →
      ∀ c : ι → ℝ, (∀ τ, NormLeOne (A τ) (c τ)) → NormLeAll T (∏ τ, c τ)

def TensorNormEq : Prop :=
  ∀ (ι : Type) [Fintype ι] (n n' : ℕ) (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)) (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam'),
    IsTensorMap A T → ∀ c : ι → ℝ, (∀ τ, IsLeast {d : ℝ | NormLeOne (A τ) d} (c τ)) →
      IsLeast {d : ℝ | NormLeAll T d} (∏ τ, c τ)

theorem IsTensorMap.unique {lam : ι → DomWeight n} {lam' : ι → DomWeight n'}
    {A : ∀ τ, nablaSq ℂ n (lam τ) →ₗ[ℂ] nablaSq ℂ n' (lam' τ)} {T T' : VV ℂ lam →ₗ[ℂ] VV ℂ lam'}
    (h : IsTensorMap A T) (h' : IsTensorMap A T') : T = T' := by
  apply LinearMap.ext
  rintro ⟨F, hF⟩
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact (h fun τ => ⟨f τ, hf τ⟩).trans (h' fun τ => ⟨f τ, hf τ⟩).symm
  | zero => exact (map_zero T).trans (map_zero T').symm
  | add x y hx hy ihx ihy =>
    have e : T (⟨x, hx⟩ + ⟨y, hy⟩) = T' (⟨x, hx⟩ + ⟨y, hy⟩) := by rw [map_add, map_add, ihx, ihy]
    exact e
  | smul a x hx ih =>
    have e : T (a • ⟨x, hx⟩) = T' (a • ⟨x, hx⟩) := by rw [map_smul, map_smul, ih]
    exact e

example (lam : ι → DomWeight n) : IsTensorMap (lam := lam) (lam' := lam) (fun _ => LinearMap.id) LinearMap.id :=
  fun _ => rfl

example (lam : DomWeight n) : NormLeOne (lam := lam) (lam' := lam) LinearMap.id 1 :=
  ⟨zero_le_one, fun f => by simp⟩

end GlobalTheory.IndefiniteRowSideFullHecke.TensorNormSquareBounds

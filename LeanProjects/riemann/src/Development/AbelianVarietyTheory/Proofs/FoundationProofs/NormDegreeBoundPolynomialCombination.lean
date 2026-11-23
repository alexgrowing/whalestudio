import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormForm

open Polynomial

namespace GlobalTheory.NormDegree

noncomputable section

variable {k A : Type} [Field k] [CommRing A] [Algebra k[X] A] {n : ℕ}

theorem natDegree_norm_of_coord_degree : ∀ (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A), ∃ (c : ℕ) (lam : Fin n → k),
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) → (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < d) → (∑ i, (C (lam i) * X ^ d + p i) • b i) ≠ 0 ∧ (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c) := by
  first
  | exact @_root_.GlobalTheory.NormFormBound.norm_degree
  | exact _root_.GlobalTheory.NormFormBound.norm_degree
  | (apply _root_.GlobalTheory.NormFormBound.norm_degree <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormFormBound.norm_degree <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormFormBound.norm_degree <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormFormBound.norm_degree ..)

end

end GlobalTheory.NormDegree

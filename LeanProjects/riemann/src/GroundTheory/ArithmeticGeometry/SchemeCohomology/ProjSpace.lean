import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjTwistAway
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

variable (A : Type u) [CommRing A] (n : ℕ)

abbrev grading : ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A) :=
  homogeneousSubmodule (Fin (n + 1)) A

end ProjSpace

open ProjSpace

abbrev projectiveSpace (A : Type u) [CommRing A] (n : ℕ) : Scheme.{u} := Proj (grading A n)

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

def stdOpen (A : Type u) [CommRing A] (n : ℕ) (j : Fin (n + 1)) : (projectiveSpace A n).Opens :=
  Proj.basicOpen (grading A n) (X j)

def xprod {p : ℕ} (i : Fin p → Fin (n + 1)) : MvPolynomial (Fin (n + 1)) A := ∏ a, X (i a)

lemma xprod_mem {p : ℕ} (i : Fin p → Fin (n + 1)) : xprod (A := A) i ∈ grading A n p := by
  have := IsHomogeneous.prod (Finset.univ : Finset (Fin p)) (fun a => (X (i a) : MvPolynomial _ A))
    (fun _ => 1) (fun a _ => isHomogeneous_X A (i a))
  simpa [xprod] using this

lemma X_mem (j : Fin (n + 1)) : (X j : MvPolynomial (Fin (n + 1)) A) ∈ grading A n 1 :=
  isHomogeneous_X A j

lemma xprod_succ {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    xprod (A := A) i = X (i 0) * xprod (A := A) (i ∘ Fin.succ) := by
  simp [xprod, Fin.prod_univ_succ]

lemma inter_stdOpen {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i =
      Proj.basicOpen (grading A n) (xprod i) := by
  ext x
  change x ∈ inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i ↔ _
  rw [mem_inter_iff]
  change (∀ a, x ∈ stdOpen A n (i a)) ↔ x ∈ Proj.basicOpen (grading A n) (xprod i)
  change (∀ a, X (i a) ∉ x.asHomogeneousIdeal.toIdeal) ↔
    (∏ a, X (i a)) ∉ x.asHomogeneousIdeal.toIdeal
  have := x.isPrime
  rw [Ideal.IsPrime.prod_mem_iff]
  simp

lemma isAffineOpen_inter {p : ℕ} (i : Fin (p + 1) → Fin (n + 1)) :
    IsAffineOpen (inter (X := (projectiveSpace A n).toTopCat) (stdOpen A n) i) := by
  rw [inter_stdOpen]
  exact Proj.isAffineOpen_basicOpen (grading A n) (xprod i) (xprod_mem i) (Nat.succ_pos p)

lemma isAffineOpen_stdOpen (j : Fin (n + 1)) : IsAffineOpen (stdOpen A n j) :=
  Proj.isAffineOpen_basicOpen (grading A n) (X j) (X_mem j) Nat.one_pos

lemma iSup_stdOpen : ⨆ j, stdOpen A n j = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  intro p hp
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  subst hm0
  have h0 : GradedRing.proj (grading A n) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' p 0 : homogeneousSubmodule (Fin (n + 1)) A 0) :
    MvPolynomial (Fin (n + 1)) A) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at h0
  exact (MvPolynomial.mem_support_iff.mp hm) h0

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh

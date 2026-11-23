import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.Affine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Toric

universe u

open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Polynomial

section HalfSpace

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] (φ : G →+ ℤ)

def LowerBound (f : AddMonoidAlgebra k G) (a : ℤ) : Prop :=
  ∀ m ∈ f.coeff.support, a ≤ φ m

noncomputable def degPart (f : AddMonoidAlgebra k G) (a : ℤ) : AddMonoidAlgebra k G :=
  ofCoeff (f.coeff.filter fun m => φ m = a)

variable {φ}

theorem LowerBound.mono {f : AddMonoidAlgebra k G} {a b : ℤ} (h : LowerBound φ f a) (hab : b ≤ a) :
    LowerBound φ f b :=
  fun m hm => hab.trans (h m hm)

theorem lowerBound_zero (a : ℤ) : LowerBound φ (0 : AddMonoidAlgebra k G) a := by
  intro m hm; simp at hm

theorem LowerBound.add {f g : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a)
    (hg : LowerBound φ g a) : LowerBound φ (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (Finsupp.support_add (by simpa using hm)) with h | h
  · exact hf m h
  · exact hg m h

theorem LowerBound.neg {f : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a) :
    LowerBound φ (-f) a := by
  intro m hm
  exact hf m (by simpa using hm)

theorem LowerBound.sum {ι : Type*} (s : Finset ι) {f : ι → AddMonoidAlgebra k G} {a : ℤ}
    (hf : ∀ i ∈ s, LowerBound φ (f i) a) : LowerBound φ (∑ i ∈ s, f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lowerBound_zero a
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem LowerBound.mul {f g : AddMonoidAlgebra k G} {a b : ℤ} (hf : LowerBound φ f a)
    (hg : LowerBound φ g b) : LowerBound φ (f * g) (a + b) := by
  classical
  intro m hm
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset f g hm)
  rw [map_add]
  exact add_le_add (hf x hx) (hg y hy)

theorem lowerBound_one : LowerBound φ (1 : AddMonoidAlgebra k G) 0 := by
  intro m hm
  have := support_coeff_one_subset hm
  simp only [Finset.mem_zero] at this
  rw [this, map_zero]

theorem LowerBound.pow {f : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a) (n : ℕ) :
    LowerBound φ (f ^ n) (n * a) := by
  induction n with
  | zero => simpa using lowerBound_one
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hf
    convert this using 1
    push_cast; ring

theorem LowerBound.coeff_eq_zero {f : AddMonoidAlgebra k G} {a : ℤ} (hf : LowerBound φ f a)
    {m : G} (hm : φ m < a) : f.coeff m = 0 := by
  by_contra h
  exact absurd (hf m (Finsupp.mem_support_iff.2 h)) (not_le.2 hm)

end HalfSpace

section GroupAlgebra

variable (k : Type*) [CommRing k] [IsDomain k] [IsIntegrallyClosed k]

variable {k} {G : Type*} [AddCommGroup G] {ι : Type*} (b : Basis ι ℤ G)

noncomputable def natCombination : (ι →₀ ℕ) →+ G where
  toFun c := Finsupp.linearCombination ℤ b (c.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero)
  map_zero' := by simp
  map_add' c d := by
    rw [← map_add]
    congr 1
    exact Finsupp.mapRange_add (fun _ _ => Nat.cast_add _ _) c d

theorem repr_natCombination (c : ι →₀ ℕ) :
    b.repr (natCombination b c) = c.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero :=
  b.repr_linearCombination _

theorem natCombination_injective : Function.Injective (natCombination b) := by
  intro c d h
  have := congrArg b.repr h
  rw [repr_natCombination, repr_natCombination] at this
  ext i
  have := congrArg (fun f => f i) this
  simpa using this

variable (k) in

noncomputable def mvPolynomialEquiv :
    MvPolynomial ι k ≃ₐ[k] semigroupAlgebra k (AddMonoidHom.mrange (natCombination b)) :=
  (AlgEquiv.ofInjective (AddMonoidAlgebra.mapDomainAlgHom k k (natCombination b))
      (mapDomain_injective (natCombination_injective b))).trans
    (Subalgebra.equivOfEq _ _ (by
      apply le_antisymm
      · rintro _ ⟨f, rfl⟩
        induction f using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add f g hf hg => rw [map_add]; exact Subalgebra.add_mem _ hf hg
        | single c a =>
          have e : mapDomainAlgHom k k (natCombination b) (single c a) =
              single (natCombination b c) a := by simp
          change mapDomainAlgHom k k (natCombination b) (single c a) ∈ _
          rw [e]
          exact single_mem_semigroupAlgebra (AddMonoidHom.mem_mrange.2 ⟨c, rfl⟩) a
      · rw [semigroupAlgebra_eq_adjoin, Algebra.adjoin_le_iff]
        rintro _ ⟨s, ⟨c, rfl⟩, rfl⟩
        exact ⟨single c 1, by simp⟩))

end GroupAlgebra

section Normal

variable {k : Type*} [CommRing k] [IsDomain k] [IsIntegrallyClosed k]

variable {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

end Normal

end GroundTheory.Arith.Toric

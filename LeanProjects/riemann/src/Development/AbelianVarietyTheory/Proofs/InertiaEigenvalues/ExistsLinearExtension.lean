import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne

namespace GlobalTheory.PsChar

section Multilinear

variable {R A : Type*} [CommRing A] [Ring R] [Algebra A R]

theorem alt_update_smul_add (T : R →ₗ[A] A) :
    ∀ (n : ℕ) (x : Fin n → R) (i : Fin n) (a : A) (u v : R),
      alt (fun r => T r) n (Function.update x i (a • u + v)) =
        a * alt (fun r => T r) n (Function.update x i u) +
          alt (fun r => T r) n (Function.update x i v)
  | 0, _, i, _, _, _ => i.elim0
  | n + 1, x, i, a, u, v => by
    have ih := alt_update_smul_add T n
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [alt, Fin.tail_update_zero, Function.update_self, add_mul, smul_mul_assoc, ih,
        map_add, map_smul, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    · have h0 : ∀ w : R, Function.update x k.succ w 0 = x 0 := fun w =>
        Function.update_of_ne (Fin.succ_ne_zero k).symm _ _
      have key : ∀ j : Fin n,
          alt (fun r => T r) n (Function.update (Function.update (Fin.tail x) k (a • u + v)) j
            (x 0 * Function.update (Fin.tail x) k (a • u + v) j)) =
          a * alt (fun r => T r) n (Function.update (Function.update (Fin.tail x) k u) j
            (x 0 * Function.update (Fin.tail x) k u j)) +
          alt (fun r => T r) n (Function.update (Function.update (Fin.tail x) k v) j
            (x 0 * Function.update (Fin.tail x) k v j)) := by
        intro j
        by_cases hj : j = k
        · subst hj
          simp only [Function.update_self, Function.update_idem, mul_add, mul_smul_comm, ih]
        · simp only [Function.update_of_ne hj, Function.update_comm (Ne.symm hj), ih]
      simp only [alt, Fin.tail_update_succ, h0, key, ih, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

noncomputable def altMultilinear (T : R →ₗ[A] A) (n : ℕ) :
    MultilinearMap A (fun _ : Fin n => R) A :=
  MultilinearMap.mk' (alt (fun r => T r) n)
    (fun x i u v => by simpa using alt_update_smul_add T n x i 1 u v)
    (fun x i a u => by
      have h0 : alt (fun r => T r) n (Function.update x i 0) = 0 := by
        have := alt_update_smul_add T n x i 1 0 0
        simpa using this
      have := alt_update_smul_add T n x i a u 0
      simpa [h0] using this)

theorem altMultilinear_apply (T : R →ₗ[A] A) (n : ℕ) (x : Fin n → R) :
    altMultilinear T n x = alt (fun r => T r) n x := rfl

end Multilinear

theorem alt_comp_monoidHom {M N A : Type*} [Monoid M] [Monoid N] [CommRing A] (f : M →* N)
    (T : N → A) :
    ∀ (n : ℕ) (x : Fin n → M), alt T n (fun i => f (x i)) = alt (fun g => T (f g)) n x
  | 0, _ => rfl
  | n + 1, x => by
    have ih := alt_comp_monoidHom f T n
    have ht : Fin.tail (fun i => f (x i)) = fun i => f (Fin.tail x i) := rfl
    have hu : ∀ i : Fin n, Function.update (fun i => f (Fin.tail x i)) i (f (x 0) * f (Fin.tail x i)) =
        fun j => f (Function.update (Fin.tail x) i (x 0 * Fin.tail x i) j) := by
      intro i
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    simp only [alt, ht, hu, ih]

theorem exists_linear_extension (M A : Type) [Monoid M] [CommRing A] (d : ℕ) (T : M → A)
    (h : IsPsChar d T) :
    ∃ T' : MonoidAlgebra A M →ₗ[A] A, (∀ g, T' (MonoidAlgebra.of A M g) = T g) ∧
      IsPsChar d (fun x => T' x) := by
  let b : Module.Basis M A (MonoidAlgebra A M) := MonoidAlgebra.basis M A
  have hb : ∀ g, b g = MonoidAlgebra.of A M g := fun g => by simp [b]
  let T' : MonoidAlgebra A M →ₗ[A] A := b.constr A T
  have hT : ∀ g, T' (MonoidAlgebra.of A M g) = T g := fun g => by
    rw [← hb]; exact b.constr_basis A T g
  refine ⟨T', hT, ?_, ?_, ?_⟩
  · rw [← (MonoidAlgebra.of A M).map_one, hT, h.one]
  · intro x y
    have : (LinearMap.mul A (MonoidAlgebra A M)).compr₂ T' =
        (LinearMap.mul A (MonoidAlgebra A M)).flip.compr₂ T' := by
      refine b.ext fun g => b.ext fun k => ?_
      simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, LinearMap.mul_apply', hb,
        ← map_mul, hT]
      exact h.comm g k
    simpa using LinearMap.congr_fun₂ this x y
  · intro x
    have : altMultilinear T' (d + 1) = 0 := by
      refine Module.Basis.ext_multilinear (fun _ => b) fun g => ?_
      rw [altMultilinear_apply]
      simp only [hb, alt_comp_monoidHom, hT]
      exact h.alt_eq_zero g
    rw [← altMultilinear_apply, this]
    rfl

end GlobalTheory.PsChar

import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators

open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem lift_single {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) (v : ι → ℝ)
    (p : MvPolynomial ι ℂ) : lift x τ (AddMonoidAlgebra.single v p) = aeval x p * τ (Multiplicative.ofAdd v) := by
  simp [lift, AddMonoidAlgebra.liftNCRingHom]

private theorem hom_ext {ι A : Type} [CommRing A] (f g : EP ι →+* A)
    (h1 : ∀ c : ℂ, f (AddMonoidAlgebra.single 0 (C c)) = g (AddMonoidAlgebra.single 0 (C c)))
    (h2 : ∀ i, f (AddMonoidAlgebra.single 0 (X i)) = g (AddMonoidAlgebra.single 0 (X i)))
    (h3 : ∀ v, f (AddMonoidAlgebra.single v 1) = g (AddMonoidAlgebra.single v 1)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun p => ?_) h3
  have : f.comp (AddMonoidAlgebra.singleZeroRingHom) = g.comp AddMonoidAlgebra.singleZeroRingHom :=
    MvPolynomial.ringHom_ext (fun c => h1 c) (fun i => h2 i)
  exact RingHom.congr_fun this p

theorem UpperTheory.ConvolutionTheory.FX.subst :
    PositivityTheory.Rg.Fx.Subst := by
  intro ι ι' _ _ Λ₀ M f
  refine ⟨fun lam => ?_, fun ι'' _ Λ₁ N => ?_⟩
  · refine RingHom.congr_fun (hom_ext ((ev lam).comp (aff Λ₀ M)) _ ?_ ?_ ?_) f
    · intro c
      simp [aff, ev, lift_single, AddMonoidAlgebra.coe_algebraMap]
    · intro i
      simp [aff, ev, lift_single, lin]
    · intro v
      simp only [aff, ev, lift_single, RingHom.comp_apply, map_one, one_mul, affChar, expChar, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, ← Complex.exp_add]
      congr 1
      simp only [Matrix.vecMul, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_add, Finset.mul_sum,
        Finset.sum_add_distrib, mul_assoc]
      rw [Finset.sum_comm]
  · refine RingHom.congr_fun (hom_ext ((aff Λ₁ N).comp (aff Λ₀ M)) _ ?_ ?_ ?_) f
    · intro c
      simp [aff, lift_single, AddMonoidAlgebra.coe_algebraMap]
    · intro i
      have e : ∀ p : MvPolynomial ι' ℂ, aeval (fun j => (AddMonoidAlgebra.single 0 (C (Λ₁ j) + lin (N j)) : EP ι'')) p =
          AddMonoidAlgebra.single 0 (aeval (fun j => (C (Λ₁ j) + lin (N j) : MvPolynomial ι'' ℂ)) p) := fun p => by
        induction p using MvPolynomial.induction_on with
        | C a => simp [AddMonoidAlgebra.coe_algebraMap]
        | add p q hp hq => rw [map_add, map_add, hp, hq, AddMonoidAlgebra.single_add]
        | mul_X p j hp => rw [map_mul, map_mul, hp, aeval_X, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]
      simp only [aff, lift_single, RingHom.comp_apply, aeval_X, ofAdd_zero, map_one, mul_one, e]
      congr 1
      simp only [lin, map_add, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc, add_assoc]
      rw [Finset.sum_comm (s := (Finset.univ : Finset ι''))]
    · intro v
      simp only [aff, lift_single, RingHom.comp_apply, map_one, one_mul, affChar, expChar, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, aeval_C, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single_mul_single, zero_add,
        algebraMap_eq, ← C_mul, ← Complex.exp_add, Matrix.vecMul_vecMul]
      congr 3
      simp only [Matrix.vecMul, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_add, Finset.mul_sum,
        Finset.sum_add_distrib, mul_assoc]
      rw [Finset.sum_comm]

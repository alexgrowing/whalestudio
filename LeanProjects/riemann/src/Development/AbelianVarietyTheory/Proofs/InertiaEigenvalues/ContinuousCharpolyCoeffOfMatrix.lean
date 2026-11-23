import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf

theorem continuous_charpoly_coeff_of_matrix {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by

  have key : ∀ M : Matrix (Fin n) (Fin n) K, M.charpoly.coeff i =
      MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := fun M =>
    (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K)
      (fun p : Fin n × Fin n => M p.1 p.2) i).symm
  have hfun : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) = fun M =>
      MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := funext key
  rw [hfun]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)

theorem charpoly_eq_of_dense :
    ∀ (Γ : Type) [TopologicalSpace Γ] (K : Type) [CommRing K] [TopologicalSpace K]
      [IsTopologicalRing K] [T2Space K] (n : ℕ) (a b : Γ → Matrix (Fin n) (Fin n) K) (S : Set Γ),
      Dense S → Continuous a → Continuous b → (∀ g ∈ S, (a g).charpoly = (b g).charpoly) →
      ∀ g, (a g).charpoly = (b g).charpoly := by
  intro Γ _ K _ _ _ _ n a b S hS ha hb hab g

  ext i
  have hc : ∀ c : Γ → Matrix (Fin n) (Fin n) K, Continuous c →
      Continuous fun x => (c x).charpoly.coeff i :=
    fun c hc => (continuous_charpoly_coeff_of_matrix n i).comp hc
  have heq := Continuous.ext_on hS (hc a ha) (hc b hb) (fun x hx => by simp only [hab x hx])
  exact congrFun heq g

end GlobalTheory.TypeLeaf

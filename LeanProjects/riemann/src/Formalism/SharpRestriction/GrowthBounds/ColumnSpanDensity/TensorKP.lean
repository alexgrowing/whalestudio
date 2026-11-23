import Mathlib

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

private theorem tm_comap {S α : Type} [Fintype S] [DecidableEq S] (n : S → α →₀ ℕ) (s : S) :
    (∑ t, Finsupp.mapDomain (fun v => (t, v)) (n t)).comapDomain (fun v => (s, v))
      (Prod.mk_right_injective s).injOn = n s := by
  ext a
  rw [Finsupp.comapDomain_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply (Prod.mk_right_injective s) (n s) a
  · intro t _ hts
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    exact hts (congrArg Prod.fst hv)
  · intro h
    exact absurd (Finset.mem_univ s) h

theorem tensorMap {K : Type} [Field K] {S α B : Type} [Fintype S] [DecidableEq S] [CommRing B]
    [Algebra K B] (g : S → MvPolynomial α K →ₗ[K] B) :
    ∃ F : MvPolynomial (S × α) K →ₗ[K] B, ∀ P : S → MvPolynomial α K,
      F (∏ s, rename (fun v => (s, v)) (P s)) = ∏ s, g s (P s) := by
  classical
  let F : MvPolynomial (S × α) K →ₗ[K] B :=
    (MvPolynomial.basisMonomials (S × α) K).constr K
      (fun m => ∏ s, g s (monomial (m.comapDomain (fun v => (s, v))
        (Prod.mk_right_injective s).injOn) 1))
  refine ⟨F, ?_⟩
  have key : F.compMultilinearMap
      ((MultilinearMap.mkPiAlgebra K S (MvPolynomial (S × α) K)).compLinearMap
        (fun s => (rename (R := K) (fun v : α => (s, v))).toLinearMap)) =
      (MultilinearMap.mkPiAlgebra K S B).compLinearMap g := by
    apply Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials α K)
    intro n
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, coe_basisMonomials,
      rename_monomial]
    rw [← monomial_sum_one]
    have h := (MvPolynomial.basisMonomials (S × α) K).constr_basis K
      (fun m => ∏ s, g s (monomial (m.comapDomain (fun v => (s, v))
        (Prod.mk_right_injective s).injOn) 1))
      (∑ t, Finsupp.mapDomain (fun v => (t, v)) (n t))
    rw [coe_basisMonomials] at h
    refine h.trans ?_
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [tm_comap]
  intro P
  have := congrArg (fun f => f P) key
  simpa using this

end Formalism.MainNotions.flipOneThree.Pf.KP

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

end Formalism.MainNotions.flipOneThree.Pf.KP

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

end Formalism.MainNotions.flipOneThree.Pf.KP

open MvPolynomial

namespace Formalism.MainNotions.flipOneThree.Pf.KP

private theorem rg_prod_mem {R A : Type} [CommSemiring R] [CommSemiring A] [Algebra R A]
    {T : Type} [DecidableEq T] (U : Finset T) (M : T → Submodule R A) (z : T → A)
    (hz : ∀ s, z s ∈ M s) : ∏ s ∈ U, z s ∈ ∏ s ∈ U, M s := by
  induction U using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Submodule.one_le.mp (le_refl (1 : Submodule R A))
  | insert a U ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Submodule.mul_mem_mul (hz a) ih

theorem regroup {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {T α : Type} [Fintype T]
    [DecidableEq T] (N : T × Bool → Submodule R (MvPolynomial α K))
    (y : T → MvPolynomial (Bool × α) K)
    (hy : ∀ s, y s ∈ Submodule.span R {P | ∃ F : Bool → MvPolynomial α K,
      (∀ b, F b ∈ N (s, b)) ∧ P = ∏ b, rename (fun v => (b, v)) (F b)}) :
    ∏ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R {P | ∃ F : T × Bool → MvPolynomial α K,
        (∀ x, F x ∈ N x) ∧ P = ∏ x, rename (fun v => (x, v)) (F x)} := by
  classical
  set G : T → Set (MvPolynomial (Bool × α) K) := fun s => {P | ∃ F : Bool → MvPolynomial α K,
      (∀ b, F b ∈ N (s, b)) ∧ P = ∏ b, rename (fun v => (b, v)) (F b)} with hG
  let ρ : ∀ s : T, MvPolynomial (Bool × α) K →ₗ[R] MvPolynomial ((T × Bool) × α) K := fun s =>
    ((rename (fun v : Bool × α => ((s, v.1), v.2)) :
      MvPolynomial (Bool × α) K →ₐ[K] MvPolynomial ((T × Bool) × α) K).restrictScalars R).toLinearMap
  have h1 : ∀ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R (ρ s '' G s) := by
    intro s
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem (f := ρ s) (hy s)
  have h2 := rg_prod_mem Finset.univ (fun s => Submodule.span R (ρ s '' G s)) _ h1
  rw [Submodule.prod_span] at h2
  refine Submodule.span_mono ?_ h2
  intro P hP
  rw [Set.mem_fintype_prod] at hP
  obtain ⟨g, hg, rfl⟩ := hP
  choose a ha hag using hg
  choose F hF hFa using ha
  refine ⟨fun x => F x.1 x.2, fun x => hF x.1 x.2, ?_⟩
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← hag s, hFa s]
  show rename (fun v : Bool × α => ((s, v.1), v.2)) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [rename_rename]
  rfl

end Formalism.MainNotions.flipOneThree.Pf.KP

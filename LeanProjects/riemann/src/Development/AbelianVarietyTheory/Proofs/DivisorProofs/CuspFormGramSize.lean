import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

set_option autoImplicit false
noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.TrBasisQuot

theorem isTranscendenceBasis_quot_polynomial {k : Type} [Field k] {m : ℕ}
    (p : Polynomial (MvPolynomial (Fin m) k)) (hp : Prime p) (hdeg : 0 < p.natDegree) :
    IsTranscendenceBasis k (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
  classical
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  let φ : MvPolynomial (Fin m) k →ₐ[k] Polynomial (MvPolynomial (Fin m) k) ⧸ Ideal.span {p} :=
    (Ideal.Quotient.mkₐ k (Ideal.span {p})).comp (IsScalarTower.toAlgHom k (MvPolynomial (Fin m) k) _)
  have hφ : ∀ b, φ b = Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C b) := fun b => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    rw [hφ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hb
    by_contra hb0
    have := Polynomial.natDegree_le_of_dvd hb (Polynomial.C_ne_zero.2 hb0)
    rw [Polynomial.natDegree_C] at this
    omega
  have haev : MvPolynomial.aeval (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) = φ :=
    MvPolynomial.algHom_ext fun j => by simp [hφ]
  have hind : AlgebraicIndependent k (fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
    rw [algebraicIndependent_iff_injective_aeval, haev]
    exact hinj
  rw [hind.isTranscendenceBasis_iff_isAlgebraic]
  have hS : ∀ b, φ b ∈ Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))) := by
    intro b
    rw [Algebra.adjoin_range_eq_range_aeval, haev]
    exact AlgHom.mem_range_self φ b
  let ψ := RingHom.codRestrict φ.toRingHom (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j)))) (fun b => hS b)
  have hψ : Function.Injective ψ := fun a b h => hinj (congrArg Subtype.val h)
  have hr : IsAlgebraic (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))))
      (Ideal.Quotient.mk (Ideal.span {p}) Polynomial.X) := by
    refine ⟨p.map ψ, (Polynomial.map_ne_zero_iff hψ).2 hp.ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hc : (algebraMap _ (Polynomial (MvPolynomial (Fin m) k) ⧸ Ideal.span {p})).comp ψ =
        (Ideal.Quotient.mk (Ideal.span {p})).comp Polynomial.C := RingHom.ext fun b => rfl
    rw [hc, ← Polynomial.hom_eval₂, Polynomial.eval₂_C_X, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self p
  have htop : Algebra.adjoin (Algebra.adjoin k (Set.range fun j : Fin m =>
      Ideal.Quotient.mk (Ideal.span {p}) (Polynomial.C (MvPolynomial.X j))))
      {Ideal.Quotient.mk (Ideal.span {p}) Polynomial.X} = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine Polynomial.induction_on q (fun b => ?_) (fun f g hf hg => ?_) (fun n b ih => ?_)
    · exact Subalgebra.algebraMap_mem _ (⟨φ b, hS b⟩ : Algebra.adjoin k _)
    · rw [map_add]
      exact add_mem hf hg
    · rw [pow_succ, ← mul_assoc, map_mul]
      exact mul_mem ih (Algebra.subset_adjoin rfl)
  have h1 := (Algebra.isAlgebraic_adjoin_singleton_iff).2 hr
  exact ⟨fun z => h1 z (by rw [htop]; trivial)⟩

theorem trBasis_mod_irreducible : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F),
    AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) →
    ∀ t : A, Irreducible t → Prime t ∧ ∃ m : ℕ, d = m + 1 ∧ ∃ y : Fin m → A,
      IsTranscendenceBasis k (fun j => Ideal.Quotient.mk (Ideal.span {t}) (y j)) := by
  intro k F _ _ _ d u hu A hA t ht
  subst hA
  classical
  have ht0 : Irreducible (hu.aevalEquiv.symm t) :=
    (MulEquiv.irreducible_iff hu.aevalEquiv.symm.toMulEquiv).2 ht
  cases d with
  | zero =>
    exfalso
    have h := MvPolynomial.eq_C_of_isEmpty (hu.aevalEquiv.symm t)
    apply ht0.not_isUnit
    rw [h]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 fun hc => ht0.ne_zero ?_)
    rw [h, hc, map_zero]
  | succ m =>
    obtain ⟨i, hi⟩ : ∃ i, (hu.aevalEquiv.symm t).degreeOf i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h0 : (hu.aevalEquiv.symm t).totalDegree = 0 := by
        rw [MvPolynomial.totalDegree_eq_zero_iff]
        intro mm hmm x
        have := MvPolynomial.monomial_le_degreeOf x hmm
        rw [hcon x] at this
        omega
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
      apply ht0.not_isUnit
      rw [h0]
      refine IsUnit.map _ (isUnit_iff_ne_zero.2 fun hc => ht0.ne_zero ?_)
      rw [h0, hc, map_zero]
    let E := hu.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin (m + 1)) i)).trans
      (MvPolynomial.finSuccEquiv k m))
    have hdeg : 0 < (E t).natDegree := by
      have h1 : (E t).natDegree = ((MvPolynomial.rename (Equiv.swap (0 : Fin (m + 1)) i))
          (hu.aevalEquiv.symm t)).degreeOf 0 :=
        MvPolynomial.natDegree_finSuccEquiv _
      have h2 := MvPolynomial.degreeOf_rename_of_injective (Equiv.swap (0 : Fin (m + 1)) i).injective
        (p := hu.aevalEquiv.symm t) i
      rw [Equiv.swap_apply_right] at h2
      rw [h1, h2]
      omega
    have hpE : Prime (E t) :=
      ((MulEquiv.irreducible_iff E.toMulEquiv).2 ht).prime
    have hpt : Prime t := (MulEquiv.prime_iff E.toMulEquiv).1 hpE
    refine ⟨hpt, m, rfl, fun j => E.symm (Polynomial.C (MvPolynomial.X j)), ?_⟩
    have hI : Ideal.span {E t} = (Ideal.span {t}).map (E : _ →+* _) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    have hb := (Ideal.quotientEquivAlg (Ideal.span {t}) (Ideal.span {E t}) E hI).symm.isTranscendenceBasis
      (GlobalTheory.TrBasisQuot.isTranscendenceBasis_quot_polynomial (E t) hpE hdeg)
    have hfun : (⇑((Ideal.span {t}).quotientEquivAlg (Ideal.span {E t}) E hI).symm ∘ fun j : Fin m =>
        (Ideal.Quotient.mk (Ideal.span {E t})) (Polynomial.C (MvPolynomial.X j))) =
        fun j => Ideal.Quotient.mk (Ideal.span {t}) (E.symm (Polynomial.C (MvPolynomial.X j))) := by
      funext j
      simp only [Function.comp_apply, Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]
    rw [hfun] at hb
    exact hb

end GlobalTheory.TrBasisQuot

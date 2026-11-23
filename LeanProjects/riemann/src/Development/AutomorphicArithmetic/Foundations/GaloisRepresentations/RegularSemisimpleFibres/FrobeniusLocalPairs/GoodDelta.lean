import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormPoly
import GroundTheory.LocalFields.Uniqueness

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section Alg

variable {n : ℕ}

private theorem map_aeval_matrix {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (p : R[X]) :
    (aeval A p).map f = aeval (A.map f) (p.map f) := by
  have h := Polynomial.hom_eval₂ p (algebraMap R (Matrix (Fin n) (Fin n) R))
    (f.mapMatrix (m := Fin n)) A
  have hc : (f.mapMatrix (m := Fin n)).comp (algebraMap R (Matrix (Fin n) (Fin n) R)) =
      (algebraMap S (Matrix (Fin n) (Fin n) S)).comp f := by
    ext x i j
    simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply, apply_ite f]
  rw [hc] at h
  rw [aeval_def, aeval_def, eval₂_map]
  exact h

private theorem commute_aeval {R : Type} [CommRing R] {x A : Matrix (Fin n) (Fin n) R}
    (h : Commute x A) (p : R[X]) : Commute x (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial m a =>
    rw [aeval_monomial]
    exact Commute.mul_right (Algebra.commutes a x).symm (h.pow_right m)

private theorem conj_aeval {R : Type} [CommRing R] (g : GL (Fin n) R)
    (A : Matrix (Fin n) (Fin n) R) (p : R[X]) :
    ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * aeval A p * (g : Matrix (Fin n) (Fin n) R) =
      aeval (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * A * (g : Matrix (Fin n) (Fin n) R)) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, ← hp, ← hq, mul_add, add_mul]
  | monomial m a =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow']
    simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]

end Alg

section Int

variable {K : Type} [Field K] [ValuativeRel K]

private theorem lifts_of_int (q : K[X]) (h : ∀ i, valuation K (q.coeff i) ≤ 1) :
    q ∈ Polynomial.lifts (algebraMap 𝒪[K] K) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro i
  exact ⟨⟨_, (Valuation.mem_integer_iff _ _).2 (h i)⟩, rfl⟩

private theorem lift_aeval {n : ℕ} (Y : Matrix (Fin n) (Fin n) 𝒪[K]) {q : K[X]}
    (h : q ∈ Polynomial.lifts (algebraMap 𝒪[K] K)) :
    ∃ C : Matrix (Fin n) (Fin n) 𝒪[K], C.map (algebraMap 𝒪[K] K) = aeval (Y.map (algebraMap 𝒪[K] K)) q := by
  obtain ⟨q', rfl⟩ := (Polynomial.mem_lifts _).1 h
  exact ⟨aeval Y q', map_aeval_matrix _ Y q'⟩

end Int

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.goodDelta :
    UpperTheory.Gal.InertialTypesAlt.L.GoodDelta := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb h n γ hγ
  set G : Matrix (Fin n) (Fin n) k := (γ : Matrix (Fin n) (Fin n) k) with hG
  have hmon : G.charpoly.Monic := Matrix.charpoly_monic G
  have h0 : valuation k (G.charpoly.coeff 0) = 1 := by
    have e := Matrix.det_eq_sign_charpoly_coeff G
    have hv := hγ.2
    rw [← hG, e, map_mul, map_pow, Valuation.map_neg, map_one, one_pow, one_mul] at hv
    exact hv
  obtain ⟨p, hp, hdvd⟩ := UpperTheory.Gal.InertialTypesAlt.L.normPoly k K F₀ F₁ rk rK s sb h G.charpoly hmon hγ.1 h0
  set A : Matrix (Fin n) (Fin n) K := (incl K n γ : Matrix (Fin n) (Fin n) K) with hA
  have hAG : A = G.map (algebraMap k K) := rfl
  let ps : ℕ → K[X] := fun i => p.map ((s ^ i : K ≃ₐ[k] K) : K →+* K)
  have hprod : aeval A (∏ i ∈ Finset.range (Module.finrank k K), ps i) = A := by
    obtain ⟨q, hq⟩ := hdvd
    have hz : aeval A (G.charpoly.map (algebraMap k K)) = 0 := by
      rw [← Matrix.charpoly_map, ← hAG]
      exact Matrix.aeval_self_charpoly A
    have e := congrArg (aeval A) hq
    rw [map_sub, aeval_X, map_mul, hz, zero_mul, sub_eq_zero] at e
    exact e
  have hAs : ∀ i, A.map ((s ^ i : K ≃ₐ[k] K) : K →+* K) = A := by
    intro i
    ext a b
    exact (s ^ i : K ≃ₐ[k] K).commutes ((γ : Matrix (Fin n) (Fin n) k) a b)
  have hmapps : ∀ i, (aeval A p).map ((s ^ i : K ≃ₐ[k] K) : K →+* K) = aeval A (ps i) := fun i => by
    have e := map_aeval_matrix ((s ^ i : K ≃ₐ[k] K) : K →+* K) A p
    rwa [hAs] at e
  obtain ⟨e, he⟩ : ∃ e, Module.finrank k K = e + 1 :=
    Nat.exists_eq_succ_of_ne_zero Module.finrank_pos.ne'
  let r : K[X] := ∏ i ∈ Finset.range e, ps (i + 1)
  have hps0 : ps 0 = p := by
    show p.map ((s ^ 0 : K ≃ₐ[k] K) : K →+* K) = p
    rw [pow_zero]
    exact Polynomial.map_id
  have hpr : aeval A (p * r) = A := by
    have e' := hprod
    rw [he, Finset.prod_range_succ', hps0, mul_comm] at e'
    exact e'
  have hδ1 : aeval A p * (aeval A r * (((incl K n γ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = 1 := by
    rw [← mul_assoc, ← map_mul (aeval A), hpr]
    exact Units.mul_inv _
  let δ : GL (Fin n) K := ⟨aeval A p, aeval A r * (((incl K n γ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
    hδ1, mul_eq_one_comm.1 hδ1⟩
  refine ⟨δ, ?_, ?_, ?_⟩
  · apply Units.ext
    have hj : ∀ j : Fin (Module.finrank k K),
        ((galAct (s ^ (j : ℕ)) n δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = aeval A (ps j) :=
      fun j => hmapps j
    have e1 : ((List.ofFn fun j : Fin (Module.finrank k K) => galAct (s ^ (j : ℕ)) n δ).prod : GL (Fin n) K).val =
        (List.ofFn fun j : Fin (Module.finrank k K) => ((galAct (s ^ (j : ℕ)) n δ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).prod := by
      have e' := map_list_prod (Units.coeHom (Matrix (Fin n) (Fin n) K))
        (List.ofFn fun j : Fin (Module.finrank k K) => galAct (s ^ (j : ℕ)) n δ)
      rw [List.map_ofFn] at e'
      exact e'
    have e2 : (List.ofFn fun j : Fin (Module.finrank k K) => aeval A (ps j)).prod =
        aeval A (List.ofFn fun j : Fin (Module.finrank k K) => ps j).prod := by
      have e' := map_list_prod (aeval A) (List.ofFn fun j : Fin (Module.finrank k K) => ps j)
      rw [List.map_ofFn] at e'
      exact e'.symm
    have e3 : (List.ofFn fun j : Fin (Module.finrank k K) => ps j).prod =
        ∏ i ∈ Finset.range (Module.finrank k K), ps i := by
      rw [List.prod_ofFn, Fin.prod_univ_eq_prod_range ps]
    show ((List.ofFn fun j : Fin (Module.finrank k K) => galAct (s ^ (j : ℕ)) n δ).prod : GL (Fin n) K).val = A
    rw [e1]
    simp only [hj]
    rw [e2, e3, hprod]
  · intro x hx
    exact Commute.units_val_iff.1 (commute_aeval (Commute.units_val_iff.2 hx) p)
  · rintro g ⟨y, hy⟩
    have hB : (y : Matrix (Fin n) (Fin n) 𝒪[K]).map (algebraMap 𝒪[K] K) =
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A * (g : Matrix (Fin n) (Fin n) K) :=
      congrArg Units.val hy
    have hlp : p ∈ Polynomial.lifts (algebraMap 𝒪[K] K) := lifts_of_int p hp
    have hlr : r ∈ Polynomial.lifts (algebraMap 𝒪[K] K) :=
      Subsemiring.prod_mem _ fun i _ => lifts_of_int _ fun j => by
        rw [Polynomial.coeff_map]
        show valuation K ((s ^ (i + 1) : K ≃ₐ[k] K) (p.coeff j)) ≤ 1
        rw [GroundTheory.LocalField.valuation_algEquiv_apply k K]
        exact hp j
    obtain ⟨Cp, hCp⟩ := lift_aeval (y : Matrix (Fin n) (Fin n) 𝒪[K]) hlp
    obtain ⟨Cr, hCr⟩ := lift_aeval (y : Matrix (Fin n) (Fin n) 𝒪[K]) hlr
    have inj : Function.Injective fun M : Matrix (Fin n) (Fin n) 𝒪[K] => M.map (algebraMap 𝒪[K] K) :=
      Matrix.map_injective Subtype.val_injective
    have h1 : Cp * (Cr * ((y⁻¹ : GL (Fin n) 𝒪[K]) : Matrix (Fin n) (Fin n) 𝒪[K])) = 1 := by
      apply inj
      show (Cp * (Cr * ((y⁻¹ : GL (Fin n) 𝒪[K]) : Matrix (Fin n) (Fin n) 𝒪[K]))).map (algebraMap 𝒪[K] K) =
        (1 : Matrix (Fin n) (Fin n) 𝒪[K]).map (algebraMap 𝒪[K] K)
      rw [Matrix.map_mul, Matrix.map_mul, hCp, hCr, ← mul_assoc,
        ← map_mul (aeval ((y : Matrix (Fin n) (Fin n) 𝒪[K]).map (algebraMap 𝒪[K] K))), hB, ← conj_aeval, hpr,
        ← hB, ← Matrix.map_mul, Units.mul_inv]
    refine ⟨⟨Cp, Cr * ((y⁻¹ : GL (Fin n) 𝒪[K]) : Matrix (Fin n) (Fin n) 𝒪[K]), h1, mul_eq_one_comm.1 h1⟩, ?_⟩
    apply Units.ext
    show Cp.map (algebraMap 𝒪[K] K) =
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * aeval A p * (g : Matrix (Fin n) (Fin n) K)
    rw [hCp, hB, conj_aeval]
